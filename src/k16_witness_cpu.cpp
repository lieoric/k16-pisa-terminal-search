#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <mutex>
#include <random>
#include <sstream>
#include <string>
#include <thread>
#include <tuple>
#include <vector>

namespace {

constexpr int N = 16;
constexpr uint16_t FULL = 0xffffu;
constexpr uint64_t BASE_SEED = 0x4b31365049534135ULL;  // "K16PISA5"

struct State {
    std::array<uint16_t, N> out{};
};

struct Evaluation {
    std::array<int, N> degree{};
    std::array<int, N> second{};
    std::array<int, N> margin{};
    std::array<int, N> blockers{};
    int max_margin = std::numeric_limits<int>::min();
    int positive_count = 0;
    int positive_sum = 0;
    int positive_square_sum = 0;
    int branch_gap = 0;
    int loss = std::numeric_limits<int>::max();
    bool strong = false;
};

struct Move {
    std::array<std::pair<int, int>, 3> edges{};
    int count = 0;
};

struct Config {
    int shard = 0;
    int seconds = 60;
    int threads = 4;
    int target_degree = 7;
    int target_blockers = 1;
    bool triangle_mode = false;
    std::string output = "results/witness.json";
};

struct SharedBest {
    std::mutex mutex;
    State state{};
    Evaluation eval{};
    bool initialized = false;
    bool witness = false;
};

std::atomic<uint64_t> evaluated{0};
std::atomic<bool> stop_requested{false};

int bit_count(uint16_t value) {
    return __builtin_popcount(static_cast<unsigned int>(value));
}

int first_bit(uint16_t value) {
    return __builtin_ctz(static_cast<unsigned int>(value));
}

uint64_t splitmix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

bool arc(const State& s, int u, int v) {
    return (s.out[u] >> v) & 1u;
}

void set_arc(State& s, int u, int v, bool uv) {
    const uint16_t bu = static_cast<uint16_t>(1u << v);
    const uint16_t bv = static_cast<uint16_t>(1u << u);
    if (uv) {
        s.out[u] |= bu;
        s.out[v] &= static_cast<uint16_t>(~bv);
    } else {
        s.out[u] &= static_cast<uint16_t>(~bu);
        s.out[v] |= bv;
    }
}

void flip_edge(State& s, int u, int v) {
    const bool uv = arc(s, u, v);
    set_arc(s, u, v, !uv);
}

bool is_ring_edge(int u, int v) {
    if (u > v) std::swap(u, v);
    return (v == u + 1) || (u == 0 && v == N - 1);
}

std::vector<std::pair<int, int>> build_free_edges() {
    std::vector<std::pair<int, int>> edges;
    for (int u = 0; u < N; ++u) {
        for (int v = u + 1; v < N; ++v) {
            if (!is_ring_edge(u, v)) edges.emplace_back(u, v);
        }
    }
    return edges;
}

std::vector<std::array<int, 3>> build_free_triples() {
    std::vector<std::array<int, 3>> triples;
    for (int a = 0; a < N; ++a) {
        for (int b = a + 1; b < N; ++b) {
            for (int c = b + 1; c < N; ++c) {
                if (!is_ring_edge(a, b) && !is_ring_edge(a, c) && !is_ring_edge(b, c)) {
                    triples.push_back({a, b, c});
                }
            }
        }
    }
    return triples;
}

uint16_t reach_mask(const State& s, bool reverse) {
    std::array<uint16_t, N> graph{};
    if (!reverse) {
        graph = s.out;
    } else {
        for (int u = 0; u < N; ++u) {
            uint16_t bits = s.out[u];
            while (bits) {
                const int v = first_bit(bits);
                graph[v] |= static_cast<uint16_t>(1u << u);
                bits &= static_cast<uint16_t>(bits - 1);
            }
        }
    }

    uint16_t seen = 1u;
    uint16_t frontier = 1u;
    while (frontier) {
        uint16_t next = 0;
        uint16_t bits = frontier;
        while (bits) {
            const int u = first_bit(bits);
            next |= graph[u];
            bits &= static_cast<uint16_t>(bits - 1);
        }
        next &= static_cast<uint16_t>(FULL ^ seen);
        seen |= next;
        frontier = next;
    }
    return seen;
}

Evaluation evaluate(const State& s, int target_degree, int target_blockers) {
    Evaluation e;
    for (int v = 0; v < N; ++v) {
        uint16_t n2 = 0;
        uint16_t bits = s.out[v];
        while (bits) {
            const int u = first_bit(bits);
            n2 |= s.out[u];
            bits &= static_cast<uint16_t>(bits - 1);
        }
        n2 &= static_cast<uint16_t>(FULL ^ s.out[v]);
        n2 &= static_cast<uint16_t>(FULL ^ static_cast<uint16_t>(1u << v));

        const int d = bit_count(s.out[v]);
        const int sec = bit_count(n2);
        const uint16_t in_mask = static_cast<uint16_t>(
            (FULL ^ s.out[v]) & (FULL ^ static_cast<uint16_t>(1u << v)));
        const uint16_t blocked = static_cast<uint16_t>(in_mask & (FULL ^ n2));
        const int b = bit_count(blocked);
        const int m = sec - d;

        e.degree[v] = d;
        e.second[v] = sec;
        e.blockers[v] = b;
        e.margin[v] = m;
        e.max_margin = std::max(e.max_margin, m);
        if (m > 0) {
            ++e.positive_count;
            e.positive_sum += m;
            e.positive_square_sum += m * m;
        }
    }

    e.strong = reach_mask(s, false) == FULL && reach_mask(s, true) == FULL;
    e.branch_gap =
        std::abs(e.degree[0] - target_degree) +
        std::abs(e.blockers[0] - target_blockers);

    // Lexicographic-like scalar: first establish the selected zero branch,
    // then eliminate positive margins.  The fixed Hamiltonian cycle makes
    // strong connectivity unconditional for every generated state.
    e.loss =
        100000 * e.branch_gap +
        10000 * e.positive_count +
        200 * e.positive_sum +
        e.positive_square_sum;
    if (!e.strong) e.loss += 1000000;
    return e;
}

bool is_witness(const Evaluation& e) {
    return e.strong && e.branch_gap == 0 && e.max_margin == 0;
}

State random_state(std::mt19937_64& rng) {
    State s;
    for (int u = 0; u < N; ++u) {
        for (int v = u + 1; v < N; ++v) {
            set_arc(s, u, v, (rng() & 1u) != 0);
        }
    }
    // WLOG for any strong tournament: relabel a directed Hamiltonian cycle
    // to 0->1->...->15->0.
    for (int v = 0; v < N - 1; ++v) set_arc(s, v, v + 1, true);
    set_arc(s, N - 1, 0, true);
    return s;
}

void apply_move(State& s, const Move& move) {
    for (int i = 0; i < move.count; ++i) {
        flip_edge(s, move.edges[i].first, move.edges[i].second);
    }
}

Move random_edge_move(
    const State& s,
    const Evaluation& e,
    int target_degree,
    const std::vector<std::pair<int, int>>& free_edges,
    std::mt19937_64& rng) {
    // When vertex 0 has the wrong score, most proposals directly repair it.
    if (e.degree[0] != target_degree && (rng() % 100) < 70) {
        std::array<std::pair<int, int>, N> candidates{};
        int count = 0;
        for (const auto& edge : free_edges) {
            if (edge.first != 0 && edge.second != 0) continue;
            const int x = edge.first == 0 ? edge.second : edge.first;
            const bool zero_beats_x = arc(s, 0, x);
            if ((e.degree[0] > target_degree && zero_beats_x) ||
                (e.degree[0] < target_degree && !zero_beats_x)) {
                candidates[count++] = {0, x};
            }
        }
        if (count > 0) {
            Move move;
            move.edges[0] = candidates[rng() % count];
            move.count = 1;
            return move;
        }
    }

    Move move;
    move.edges[0] = free_edges[rng() % free_edges.size()];
    move.count = 1;
    return move;
}

Move random_triangle_or_edge_move(
    const State& s,
    const Evaluation& e,
    int target_degree,
    const std::vector<std::pair<int, int>>& free_edges,
    const std::vector<std::array<int, 3>>& triples,
    std::mt19937_64& rng) {
    // Keep enough single-edge moves to cross score-sequence strata.
    if ((rng() % 100) < 35) {
        return random_edge_move(s, e, target_degree, free_edges, rng);
    }

    for (int attempt = 0; attempt < 16; ++attempt) {
        const auto& t = triples[rng() % triples.size()];
        const int a = t[0], b = t[1], c = t[2];
        const bool forward = arc(s, a, b) && arc(s, b, c) && arc(s, c, a);
        const bool backward = arc(s, b, a) && arc(s, c, b) && arc(s, a, c);
        if (forward || backward) {
            Move move;
            move.edges[0] = {a, b};
            move.edges[1] = {b, c};
            move.edges[2] = {a, c};
            move.count = 3;
            return move;
        }
    }
    return random_edge_move(s, e, target_degree, free_edges, rng);
}

bool better(const Evaluation& a, const Evaluation& b) {
    return std::tie(a.loss, a.branch_gap, a.positive_count, a.positive_sum) <
           std::tie(b.loss, b.branch_gap, b.positive_count, b.positive_sum);
}

void publish_best(SharedBest& shared, const State& s, const Evaluation& e, int thread_id) {
    std::lock_guard<std::mutex> lock(shared.mutex);
    if (!shared.initialized || better(e, shared.eval)) {
        shared.state = s;
        shared.eval = e;
        shared.initialized = true;
        shared.witness = is_witness(e);
        std::cerr << "best thread=" << thread_id
                  << " loss=" << e.loss
                  << " branch_gap=" << e.branch_gap
                  << " positive=" << e.positive_count
                  << " max_margin=" << e.max_margin
                  << " d0=" << e.degree[0]
                  << " b0=" << e.blockers[0] << "\n";
        if (shared.witness) stop_requested.store(true, std::memory_order_relaxed);
    }
}

void worker(
    int thread_id,
    const Config& cfg,
    const std::chrono::steady_clock::time_point deadline,
    SharedBest& shared,
    const std::vector<std::pair<int, int>>& free_edges,
    const std::vector<std::array<int, 3>>& triples) {
    const uint64_t seed = splitmix64(
        BASE_SEED ^
        (static_cast<uint64_t>(cfg.shard) << 32) ^
        (static_cast<uint64_t>(thread_id) << 1) ^
        (cfg.triangle_mode ? 0x545249414e474c45ULL : 0x454447454d4f4445ULL));
    std::mt19937_64 rng(seed);

    constexpr int SAMPLE_MOVES = 6;
    constexpr int RESTART_STEPS = 12000;
    constexpr int STAGNATION_STEPS = 2500;

    while (!stop_requested.load(std::memory_order_relaxed) &&
           std::chrono::steady_clock::now() < deadline) {
        State current = random_state(rng);

        // Occasionally restart near the current global elite, with a kick.
        if ((rng() % 100) < 55) {
            std::lock_guard<std::mutex> lock(shared.mutex);
            if (shared.initialized) {
                current = shared.state;
                const int kicks = 4 + static_cast<int>(rng() % 13);
                for (int k = 0; k < kicks; ++k) {
                    const auto& edge = free_edges[rng() % free_edges.size()];
                    flip_edge(current, edge.first, edge.second);
                }
            }
        }

        Evaluation current_eval =
            evaluate(current, cfg.target_degree, cfg.target_blockers);
        evaluated.fetch_add(1, std::memory_order_relaxed);
        publish_best(shared, current, current_eval, thread_id);
        int stagnation = 0;

        for (int step = 0;
             step < RESTART_STEPS &&
             stagnation < STAGNATION_STEPS &&
             !stop_requested.load(std::memory_order_relaxed) &&
             std::chrono::steady_clock::now() < deadline;
             ++step) {
            Move chosen{};
            Evaluation chosen_eval{};
            bool chosen_set = false;

            for (int sample = 0; sample < SAMPLE_MOVES; ++sample) {
                Move move = cfg.triangle_mode
                    ? random_triangle_or_edge_move(
                          current, current_eval, cfg.target_degree,
                          free_edges, triples, rng)
                    : random_edge_move(
                          current, current_eval, cfg.target_degree,
                          free_edges, rng);
                apply_move(current, move);
                Evaluation candidate =
                    evaluate(current, cfg.target_degree, cfg.target_blockers);
                evaluated.fetch_add(1, std::memory_order_relaxed);
                apply_move(current, move);

                if (!chosen_set || better(candidate, chosen_eval)) {
                    chosen = move;
                    chosen_eval = candidate;
                    chosen_set = true;
                }
            }

            const int delta = chosen_eval.loss - current_eval.loss;
            const double progress = static_cast<double>(step) / RESTART_STEPS;
            const double temperature = 2500.0 * (1.0 - progress) + 25.0;
            const double probability =
                delta <= 0 ? 1.0 : std::exp(-static_cast<double>(delta) / temperature);
            std::uniform_real_distribution<double> uniform(0.0, 1.0);
            const bool noisy_accept = (rng() % 1000) < 15;

            if (delta <= 0 || noisy_accept || uniform(rng) < probability) {
                apply_move(current, chosen);
                const bool improved = better(chosen_eval, current_eval);
                current_eval = chosen_eval;
                stagnation = improved ? 0 : stagnation + 1;
                publish_best(shared, current, current_eval, thread_id);
            } else {
                ++stagnation;
            }
        }
    }
}

bool validate_tournament(const State& s) {
    for (int u = 0; u < N; ++u) {
        if (arc(s, u, u)) return false;
        for (int v = u + 1; v < N; ++v) {
            if (static_cast<int>(arc(s, u, v)) +
                    static_cast<int>(arc(s, v, u)) != 1) {
                return false;
            }
        }
    }
    return true;
}

State cyclic_odd(int n) {
    State s;
    for (int i = 0; i < n; ++i) {
        for (int step = 1; step <= (n - 1) / 2; ++step) {
            const int j = (i + step) % n;
            s.out[i] |= static_cast<uint16_t>(1u << j);
        }
    }
    return s;
}

State near_regular_even(int n) {
    State s;
    const int half = n / 2;
    for (int i = 0; i < n; ++i) {
        for (int j = i + 1; j < n; ++j) {
            const int delta = j - i;
            if (delta < half) {
                set_arc(s, i, j, true);
            } else if (delta > half) {
                set_arc(s, i, j, false);
            } else {
                set_arc(s, i, j, (i % 2) == 0);
            }
        }
    }
    return s;
}

bool self_test() {
    // The generic K16 evaluator cannot be used for smaller orders, so the
    // smoke gate checks the construction identities directly.
    const State k15 = cyclic_odd(15);
    for (int v = 0; v < 15; ++v) {
        if (bit_count(static_cast<uint16_t>(k15.out[v] & 0x7fffu)) != 7) {
            return false;
        }
    }
    const State k14 = near_regular_even(14);
    int six = 0, seven = 0;
    for (int v = 0; v < 14; ++v) {
        const int d = bit_count(static_cast<uint16_t>(k14.out[v] & 0x3fffu));
        six += d == 6;
        seven += d == 7;
    }
    return six == 7 && seven == 7;
}

std::string json_array(const std::array<int, N>& values) {
    std::ostringstream out;
    out << "[";
    for (int i = 0; i < N; ++i) {
        if (i) out << ",";
        out << values[i];
    }
    out << "]";
    return out.str();
}

void write_json(
    const Config& cfg,
    const SharedBest& shared,
    double wall_seconds,
    uint64_t states_evaluated) {
    std::ofstream out(cfg.output);
    if (!out) throw std::runtime_error("cannot open output path");

    const bool witness = shared.initialized && is_witness(shared.eval);
    out << "{\n";
    out << "  \"campaign\": \"K16-PISA-v5\",\n";
    out << "  \"platform\": \"github-cpu\",\n";
    out << "  \"status\": \"" << (witness ? "WITNESS" : "NO_WITNESS") << "\",\n";
    out << "  \"shard\": " << cfg.shard << ",\n";
    out << "  \"strategy\": \""
        << (cfg.target_degree == 7 ? "d7_b1" : "d6_b3")
        << (cfg.triangle_mode ? "_mixed" : "_edge") << "\",\n";
    out << "  \"target_degree\": " << cfg.target_degree << ",\n";
    out << "  \"target_blockers\": " << cfg.target_blockers << ",\n";
    out << "  \"threads\": " << cfg.threads << ",\n";
    out << "  \"wall_seconds\": " << std::fixed << std::setprecision(3)
        << wall_seconds << ",\n";
    out << "  \"states_evaluated\": " << states_evaluated << ",\n";
    out << "  \"best_loss\": " << shared.eval.loss << ",\n";
    out << "  \"best_branch_gap\": " << shared.eval.branch_gap << ",\n";
    out << "  \"best_max_margin\": " << shared.eval.max_margin << ",\n";
    out << "  \"best_positive_count\": " << shared.eval.positive_count << ",\n";
    out << "  \"out_masks\": [";
    for (int v = 0; v < N; ++v) {
        if (v) out << ",";
        out << shared.state.out[v];
    }
    out << "],\n";
    out << "  \"outdegrees\": " << json_array(shared.eval.degree) << ",\n";
    out << "  \"second_sizes\": " << json_array(shared.eval.second) << ",\n";
    out << "  \"margins\": " << json_array(shared.eval.margin) << ",\n";
    out << "  \"blockers\": " << json_array(shared.eval.blockers) << ",\n";
    out << "  \"witness_verified_in_process\": "
        << (witness && validate_tournament(shared.state) ? "true" : "false") << "\n";
    out << "}\n";
}

Config parse_args(int argc, char** argv, bool& run_self_test) {
    Config cfg;
    run_self_test = false;
    for (int i = 1; i < argc; ++i) {
        const std::string arg = argv[i];
        auto require_value = [&](const std::string& name) -> std::string {
            if (i + 1 >= argc) throw std::runtime_error("missing value for " + name);
            return argv[++i];
        };
        if (arg == "--shard") cfg.shard = std::stoi(require_value(arg));
        else if (arg == "--seconds") cfg.seconds = std::stoi(require_value(arg));
        else if (arg == "--threads") cfg.threads = std::stoi(require_value(arg));
        else if (arg == "--output") cfg.output = require_value(arg);
        else if (arg == "--self-test") run_self_test = true;
        else throw std::runtime_error("unknown argument: " + arg);
    }

    const int lane = ((cfg.shard % 4) + 4) % 4;
    cfg.target_degree = lane < 2 ? 7 : 6;
    cfg.target_blockers = cfg.target_degree == 7 ? 1 : 3;
    cfg.triangle_mode = (lane % 2) == 1;
    cfg.threads = std::max(1, cfg.threads);
    cfg.seconds = std::max(1, cfg.seconds);
    return cfg;
}

}  // namespace

int main(int argc, char** argv) {
    try {
        bool run_self_test = false;
        const Config cfg = parse_args(argc, argv, run_self_test);
        if (run_self_test) {
            const bool ok = self_test();
            std::cout << (ok ? "SELF_TEST_PASS\n" : "SELF_TEST_FAIL\n");
            return ok ? 0 : 1;
        }

        const auto start = std::chrono::steady_clock::now();
        const auto deadline = start + std::chrono::seconds(cfg.seconds);
        const auto free_edges = build_free_edges();
        const auto triples = build_free_triples();
        if (free_edges.size() != 104) {
            throw std::runtime_error("expected 104 free edges after fixing the cycle");
        }

        SharedBest shared;
        std::vector<std::thread> workers;
        for (int t = 0; t < cfg.threads; ++t) {
            workers.emplace_back(
                worker, t, std::cref(cfg), deadline, std::ref(shared),
                std::cref(free_edges), std::cref(triples));
        }
        for (auto& thread : workers) thread.join();

        const double wall_seconds =
            std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        write_json(cfg, shared, wall_seconds, evaluated.load());

        std::cout << "status="
                  << (shared.witness ? "WITNESS" : "NO_WITNESS")
                  << " shard=" << cfg.shard
                  << " loss=" << shared.eval.loss
                  << " states=" << evaluated.load()
                  << " seconds=" << std::fixed << std::setprecision(2)
                  << wall_seconds << "\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "ERROR: " << error.what() << "\n";
        return 2;
    }
}
