#include <algorithm>
#include <array>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <mutex>
#include <random>
#include <sstream>
#include <string>
#include <thread>
#include <tuple>
#include <unordered_set>
#include <vector>

namespace {

constexpr int N = 16;
constexpr int PARTITION_BUCKETS = 32;
constexpr uint16_t FULL = 0xffffu;
constexpr uint64_t BASE_SEED = 0x4b31365049534137ULL;  // "K16PISA7"
constexpr int ELITE_CAPACITY = 32;
constexpr int MOVE_CAPACITY = 20;

struct State {
    std::array<uint16_t, N> out{};
};

struct Evaluation {
    std::array<int, N> degree{};
    std::array<int, N> second{};
    std::array<int, N> margin{};
    std::array<int, N> blockers{};
    std::array<int, N> extra_blocker_defect{};
    int max_margin = std::numeric_limits<int>::min();
    int positive_count = 0;
    int positive_sum = 0;
    int positive_square_sum = 0;
    int positive_defect_sum = 0;
    int branch_gap = 0;
    int loss = std::numeric_limits<int>::max();
    bool strong = false;
};

struct Move {
    std::array<std::pair<int, int>, MOVE_CAPACITY> edges{};
    int count = 0;
};

struct Config {
    int shard = 0;
    int seconds = 60;
    int threads = 4;
    int target_degree = 7;
    int target_blockers = 1;
    int bucket = 0;
    std::string output = "results/witness.json";
};

struct SharedBest {
    struct Elite {
        State state{};
        Evaluation eval{};
    };

    std::mutex mutex;
    State state{};
    Evaluation eval{};
    std::vector<Elite> pool;
    bool initialized = false;
    bool witness = false;
};

std::atomic<uint64_t> evaluated{0};
std::atomic<uint64_t> repair_attempts{0};
std::atomic<uint64_t> repair_states{0};
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
    for (int u = 1; u < N; ++u) {
        for (int v = u + 1; v < N; ++v) {
            if (!is_ring_edge(u, v)) edges.emplace_back(u, v);
        }
    }
    return edges;
}

std::vector<std::array<int, 3>> build_free_triples() {
    std::vector<std::array<int, 3>> triples;
    for (int a = 1; a < N; ++a) {
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

int binomial(int n, int k) {
    if (k < 0 || k > n) return 0;
    if (k == 0 || k == n) return 1;
    k = std::min(k, n - k);
    int value = 1;
    for (int i = 1; i <= k; ++i) {
        value = value * (n - k + i) / i;
    }
    return value;
}

int colex_rank(uint16_t subset) {
    int rank = 0;
    int selected = 0;
    for (int position = 0; position < 13; ++position) {
        if ((subset >> position) & 1u) {
            ++selected;
            rank += binomial(position, selected);
        }
    }
    return rank;
}

uint16_t zero_subset(const State& s) {
    uint16_t subset = 0;
    for (int position = 0; position < 13; ++position) {
        if (arc(s, 0, position + 2)) {
            subset |= static_cast<uint16_t>(1u << position);
        }
    }
    return subset;
}

std::vector<uint16_t> build_zero_patterns(int target_degree, int bucket) {
    const int choose = target_degree - 1;
    std::vector<uint16_t> patterns;
    for (uint16_t subset = 0; subset < (1u << 13); ++subset) {
        if (bit_count(subset) != choose) continue;
        if (colex_rank(subset) % PARTITION_BUCKETS == bucket) {
            patterns.push_back(subset);
        }
    }
    return patterns;
}

bool in_partition(const State& s, const Config& cfg) {
    return bit_count(s.out[0]) == cfg.target_degree &&
           colex_rank(zero_subset(s)) % PARTITION_BUCKETS == cfg.bucket;
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
        int extra_defect = N;
        uint16_t incoming = in_mask;
        while (incoming) {
            const int x = first_bit(incoming);
            incoming &= static_cast<uint16_t>(incoming - 1);
            int defect = 0;
            uint16_t out_bits = s.out[v];
            while (out_bits) {
                const int u = first_bit(out_bits);
                out_bits &= static_cast<uint16_t>(out_bits - 1);
                if (arc(s, u, x)) ++defect;
            }
            if (defect > 0) extra_defect = std::min(extra_defect, defect);
        }

        e.degree[v] = d;
        e.second[v] = sec;
        e.blockers[v] = b;
        e.margin[v] = m;
        e.extra_blocker_defect[v] = extra_defect;
        e.max_margin = std::max(e.max_margin, m);
        if (m > 0) {
            ++e.positive_count;
            e.positive_sum += m;
            e.positive_square_sum += m * m;
            e.positive_defect_sum += extra_defect;
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

int64_t dynamic_energy(
    const Evaluation& e,
    const std::array<int, N>& weights) {
    int64_t value = 100000000LL * e.branch_gap;
    if (!e.strong) value += 1000000000LL;
    for (int v = 0; v < N; ++v) {
        if (e.margin[v] <= 0) continue;
        const int defect = std::min(N, e.extra_blocker_defect[v]);
        value += static_cast<int64_t>(weights[v]) *
                 (20000 + 800 * e.margin[v] +
                  40 * e.margin[v] * e.margin[v] + 120 * defect);
    }
    return value;
}

bool is_witness(const State& s, const Evaluation& e, const Config& cfg) {
    return e.strong && e.branch_gap == 0 && e.max_margin == 0 &&
           in_partition(s, cfg);
}

State random_state(
    std::mt19937_64& rng,
    const std::vector<uint16_t>& zero_patterns) {
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
    const uint16_t zero_pattern = zero_patterns[rng() % zero_patterns.size()];
    for (int position = 0; position < 13; ++position) {
        set_arc(s, 0, position + 2, (zero_pattern >> position) & 1u);
    }
    return s;
}

void apply_move(State& s, const Move& move) {
    for (int i = 0; i < move.count; ++i) {
        flip_edge(s, move.edges[i].first, move.edges[i].second);
    }
}

bool is_free_edge(int u, int v) {
    if (u == v || u == 0 || v == 0) return false;
    return !is_ring_edge(u, v);
}

bool add_move_edge(Move& move, int u, int v) {
    if (!is_free_edge(u, v) || move.count >= MOVE_CAPACITY) return false;
    if (u > v) std::swap(u, v);
    for (int i = 0; i < move.count; ++i) {
        if (move.edges[i] == std::make_pair(u, v)) return true;
    }
    move.edges[move.count++] = {u, v};
    return true;
}

int select_positive_vertex(
    const Evaluation& e,
    const std::array<int, N>& weights,
    std::mt19937_64& rng) {
    int total = 0;
    for (int v = 0; v < N; ++v) {
        if (e.margin[v] > 0) total += weights[v] * e.margin[v];
    }
    if (total == 0) return -1;
    int ticket = static_cast<int>(rng() % total);
    for (int v = 0; v < N; ++v) {
        if (e.margin[v] <= 0) continue;
        ticket -= weights[v] * e.margin[v];
        if (ticket < 0) return v;
    }
    return -1;
}

Move focused_repair_move(
    const State& s,
    const Evaluation& e,
    const std::array<int, N>& weights,
    const std::vector<std::pair<int, int>>& free_edges,
    std::mt19937_64& rng) {
    const int v = select_positive_vertex(e, weights, rng);
    if (v < 0) {
        Move fallback;
        fallback.edges[0] = free_edges[rng() % free_edges.size()];
        fallback.count = 1;
        return fallback;
    }

    // Half the time, directly raise the offender's outdegree by reversing a
    // mutable incoming edge.  This is the shortest possible degree repair.
    if ((rng() % 100) < 45) {
        std::vector<int> incoming;
        for (int x = 1; x < N; ++x) {
            if (x != v && arc(s, x, v) && is_free_edge(v, x)) incoming.push_back(x);
        }
        if (!incoming.empty()) {
            Move move;
            add_move_edge(move, v, incoming[rng() % incoming.size()]);
            return move;
        }
    }

    // Otherwise complete a nearly-blocking in-neighbour x.  The defect edges
    // are precisely u->x with u in N+(v); reversing all of them makes x beat
    // v and every out-neighbour of v, hence creates one new blocker of v.
    struct Candidate {
        int x;
        std::vector<int> defect_vertices;
    };
    std::vector<Candidate> candidates;
    for (int x = 1; x < N; ++x) {
        if (x == v || !arc(s, x, v)) continue;
        Candidate candidate{x, {}};
        bool mutable_completion = true;
        uint16_t bits = s.out[v];
        while (bits) {
            const int u = first_bit(bits);
            bits &= static_cast<uint16_t>(bits - 1);
            if (!arc(s, u, x)) continue;
            if (!is_free_edge(u, x)) {
                mutable_completion = false;
                break;
            }
            candidate.defect_vertices.push_back(u);
        }
        if (mutable_completion && !candidate.defect_vertices.empty() &&
            candidate.defect_vertices.size() <= 6) {
            candidates.push_back(std::move(candidate));
        }
    }
    if (!candidates.empty()) {
        std::sort(
            candidates.begin(), candidates.end(),
            [](const Candidate& a, const Candidate& b) {
                return a.defect_vertices.size() < b.defect_vertices.size();
            });
        const size_t window = std::min<size_t>(4, candidates.size());
        const Candidate& chosen = candidates[rng() % window];
        Move move;
        for (const int u : chosen.defect_vertices) add_move_edge(move, u, chosen.x);

        // Occasionally pair blocker completion with one local degree repair.
        if ((rng() % 100) < 30) {
            std::vector<int> incoming;
            for (int x = 1; x < N; ++x) {
                if (x != v && arc(s, x, v) && is_free_edge(v, x)) incoming.push_back(x);
            }
            if (!incoming.empty()) {
                add_move_edge(move, v, incoming[rng() % incoming.size()]);
            }
        }
        if (move.count > 0) return move;
    }

    Move fallback;
    fallback.edges[0] = free_edges[rng() % free_edges.size()];
    fallback.count = 1;
    return fallback;
}

Move random_edge_move(
    const State&,
    const Evaluation&,
    int,
    const std::vector<std::pair<int, int>>& free_edges,
    std::mt19937_64& rng) {
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
    return std::tie(
               a.loss, a.positive_defect_sum, a.branch_gap,
               a.positive_count, a.positive_sum) <
           std::tie(
               b.loss, b.positive_defect_sum, b.branch_gap,
               b.positive_count, b.positive_sum);
}

int state_distance(const State& a, const State& b) {
    int distance = 0;
    for (int u = 1; u < N; ++u) {
        for (int v = u + 1; v < N; ++v) {
            if (!is_free_edge(u, v)) continue;
            distance += arc(a, u, v) != arc(b, u, v);
        }
    }
    return distance;
}

uint64_t state_hash(const State& s) {
    uint64_t hash = 0xcbf29ce484222325ULL;
    for (const uint16_t mask : s.out) {
        hash ^= mask;
        hash *= 0x100000001b3ULL;
    }
    return hash;
}

void publish_best(
    SharedBest& shared,
    const State& s,
    const Evaluation& e,
    const Config& cfg,
    int thread_id) {
    std::lock_guard<std::mutex> lock(shared.mutex);
    if (!shared.initialized || better(e, shared.eval)) {
        shared.state = s;
        shared.eval = e;
        shared.initialized = true;
        shared.witness = is_witness(s, e, cfg);
        std::cerr << "best thread=" << thread_id
                  << " loss=" << e.loss
                  << " defect=" << e.positive_defect_sum
                  << " branch_gap=" << e.branch_gap
                  << " positive=" << e.positive_count
                  << " max_margin=" << e.max_margin
                  << " d0=" << e.degree[0]
                  << " b0=" << e.blockers[0]
                  << " bucket=" << cfg.bucket
                  << " zero_rank=" << colex_rank(zero_subset(s)) << "\n";
        if (shared.witness) stop_requested.store(true, std::memory_order_relaxed);
    }

    if (e.branch_gap == 0 && e.positive_count <= 2) {
        int close_index = -1;
        for (size_t i = 0; i < shared.pool.size(); ++i) {
            if (state_distance(s, shared.pool[i].state) < 8) {
                close_index = static_cast<int>(i);
                break;
            }
        }
        if (close_index >= 0) {
            if (better(e, shared.pool[close_index].eval)) {
                shared.pool[close_index] = {s, e};
            }
        } else if (shared.pool.size() < ELITE_CAPACITY) {
            shared.pool.push_back({s, e});
        } else {
            auto worst = std::max_element(
                shared.pool.begin(), shared.pool.end(),
                [](const SharedBest::Elite& a, const SharedBest::Elite& b) {
                    return better(a.eval, b.eval);
                });
            if (worst != shared.pool.end() && better(e, worst->eval)) {
                *worst = {s, e};
            }
        }
    }
}

bool sample_elite(
    SharedBest& shared,
    State& state,
    std::mt19937_64& rng) {
    std::lock_guard<std::mutex> lock(shared.mutex);
    if (shared.pool.empty()) {
        if (!shared.initialized) return false;
        state = shared.state;
        return true;
    }
    state = shared.pool[rng() % shared.pool.size()].state;
    return true;
}

std::vector<std::pair<int, int>> repair_kernel(
    const State& s,
    const Evaluation& e,
    int offender) {
    struct RankedEdge {
        int priority;
        int u;
        int v;
    };
    std::vector<RankedEdge> ranked;
    auto add_ranked = [&](int priority, int u, int v) {
        if (!is_free_edge(u, v)) return;
        if (u > v) std::swap(u, v);
        for (auto& item : ranked) {
            if (item.u == u && item.v == v) {
                item.priority = std::min(item.priority, priority);
                return;
            }
        }
        ranked.push_back({priority, u, v});
    };

    for (int x = 1; x < N; ++x) {
        if (x != offender) add_ranked(30, offender, x);
    }
    struct BlockerCandidate {
        int defect;
        int x;
        std::vector<int> vertices;
    };
    std::vector<BlockerCandidate> candidates;
    for (int x = 1; x < N; ++x) {
        if (x == offender || !arc(s, x, offender)) continue;
        BlockerCandidate candidate{0, x, {}};
        bool mutable_completion = true;
        uint16_t bits = s.out[offender];
        while (bits) {
            const int u = first_bit(bits);
            bits &= static_cast<uint16_t>(bits - 1);
            if (!arc(s, u, x)) continue;
            if (!is_free_edge(u, x)) {
                mutable_completion = false;
                break;
            }
            ++candidate.defect;
            candidate.vertices.push_back(u);
        }
        if (mutable_completion && candidate.defect > 0) {
            candidates.push_back(std::move(candidate));
        }
    }
    std::sort(
        candidates.begin(), candidates.end(),
        [](const BlockerCandidate& a, const BlockerCandidate& b) {
            return a.defect < b.defect;
        });
    for (size_t i = 0; i < std::min<size_t>(6, candidates.size()); ++i) {
        for (const int u : candidates[i].vertices) {
            add_ranked(candidates[i].defect, u, candidates[i].x);
        }
    }
    std::sort(
        ranked.begin(), ranked.end(),
        [](const RankedEdge& a, const RankedEdge& b) {
            return std::tie(a.priority, a.u, a.v) <
                   std::tie(b.priority, b.u, b.v);
        });
    std::vector<std::pair<int, int>> kernel;
    for (const auto& item : ranked) {
        if (kernel.size() == 20) break;
        kernel.emplace_back(item.u, item.v);
    }
    (void)e;
    return kernel;
}

bool exact_local_repair(
    State& current,
    Evaluation& current_eval,
    const std::array<int, N>& weights,
    const Config& cfg,
    const std::chrono::steady_clock::time_point deadline,
    SharedBest& shared,
    int thread_id,
    std::unordered_set<uint64_t>& seen) {
    if (current_eval.branch_gap != 0 || current_eval.positive_count != 1) {
        return false;
    }
    const uint64_t hash = state_hash(current);
    if (!seen.insert(hash).second || seen.size() > 256) return false;

    int offender = -1;
    for (int v = 0; v < N; ++v) {
        if (current_eval.margin[v] > 0) {
            offender = v;
            break;
        }
    }
    if (offender < 0) return false;
    const auto kernel = repair_kernel(current, current_eval, offender);
    if (kernel.empty()) return false;
    repair_attempts.fetch_add(1, std::memory_order_relaxed);

    State candidate = current;
    State best_state = current;
    Evaluation best_eval = current_eval;
    int64_t best_energy = dynamic_energy(current_eval, weights);
    bool found = false;
    uint64_t local_evaluated = 0;

    for (int radius = 1; radius <= 6 && !found; ++radius) {
        std::function<void(int, int)> visit = [&](int start, int remaining) {
            if (found || std::chrono::steady_clock::now() >= deadline) return;
            if (remaining == 0) {
                Evaluation e =
                    evaluate(candidate, cfg.target_degree, cfg.target_blockers);
                evaluated.fetch_add(1, std::memory_order_relaxed);
                repair_states.fetch_add(1, std::memory_order_relaxed);
                ++local_evaluated;
                const int64_t energy = dynamic_energy(e, weights);
                if (energy < best_energy ||
                    (energy == best_energy && better(e, best_eval))) {
                    best_energy = energy;
                    best_state = candidate;
                    best_eval = e;
                }
                if (is_witness(candidate, e, cfg)) {
                    best_state = candidate;
                    best_eval = e;
                    publish_best(shared, candidate, e, cfg, thread_id);
                    found = true;
                }
                return;
            }
            const int last =
                static_cast<int>(kernel.size()) - remaining;
            for (int i = start; i <= last && !found; ++i) {
                flip_edge(candidate, kernel[i].first, kernel[i].second);
                visit(i + 1, remaining - 1);
                flip_edge(candidate, kernel[i].first, kernel[i].second);
            }
        };
        visit(0, radius);
    }

    if (best_energy < dynamic_energy(current_eval, weights) ||
        better(best_eval, current_eval)) {
        current = best_state;
        current_eval = best_eval;
        publish_best(shared, current, current_eval, cfg, thread_id);
        return true;
    }
    (void)local_evaluated;
    return found;
}

void worker(
    int thread_id,
    const Config& cfg,
    const std::chrono::steady_clock::time_point deadline,
    SharedBest& shared,
    const std::vector<std::pair<int, int>>& free_edges,
    const std::vector<std::array<int, 3>>& triples,
    const std::vector<uint16_t>& zero_patterns) {
    const uint64_t seed = splitmix64(
        BASE_SEED ^
        (static_cast<uint64_t>(cfg.shard) << 32) ^
        (static_cast<uint64_t>(thread_id) << 1));
    std::mt19937_64 rng(seed);

    constexpr int SAMPLE_MOVES = 10;
    constexpr int RESTART_STEPS = 18000;
    constexpr int STAGNATION_STEPS = 3600;
    std::array<int, N> weights{};
    weights.fill(1);
    std::unordered_set<uint64_t> repair_seen;

    while (!stop_requested.load(std::memory_order_relaxed) &&
           std::chrono::steady_clock::now() < deadline) {
        State current = random_state(rng, zero_patterns);

        // Restart from a diverse elite pool, then kick far enough to leave the
        // previous basin.  This replaces the v6 single-global-elite collapse.
        if ((rng() % 100) < 70 && sample_elite(shared, current, rng)) {
            const int kicks = 6 + static_cast<int>(rng() % 19);
            for (int k = 0; k < kicks; ++k) {
                const auto& edge = free_edges[rng() % free_edges.size()];
                flip_edge(current, edge.first, edge.second);
            }
        }

        Evaluation current_eval =
            evaluate(current, cfg.target_degree, cfg.target_blockers);
        evaluated.fetch_add(1, std::memory_order_relaxed);
        publish_best(shared, current, current_eval, cfg, thread_id);
        int64_t current_energy = dynamic_energy(current_eval, weights);
        int stagnation = 0;

        for (int step = 0;
             step < RESTART_STEPS &&
             stagnation < STAGNATION_STEPS &&
             !stop_requested.load(std::memory_order_relaxed) &&
             std::chrono::steady_clock::now() < deadline;
             ++step) {
            if (current_eval.branch_gap == 0 &&
                current_eval.positive_count == 1 &&
                current_eval.max_margin == 1) {
                if (exact_local_repair(
                        current, current_eval, weights, cfg, deadline,
                        shared, thread_id, repair_seen)) {
                    current_energy = dynamic_energy(current_eval, weights);
                    stagnation = 0;
                    if (is_witness(current, current_eval, cfg)) break;
                }
            }

            Move chosen{};
            Evaluation chosen_eval{};
            int64_t chosen_energy = std::numeric_limits<int64_t>::max();
            bool chosen_set = false;

            for (int sample = 0; sample < SAMPLE_MOVES; ++sample) {
                Move move;
                const int roll = static_cast<int>(rng() % 100);
                if (roll < 68 && current_eval.positive_count > 0) {
                    move = focused_repair_move(
                        current, current_eval, weights, free_edges, rng);
                } else if (roll < 88) {
                    move = random_triangle_or_edge_move(
                          current, current_eval, cfg.target_degree,
                          free_edges, triples, rng);
                } else {
                    move = random_edge_move(
                        current, current_eval, cfg.target_degree,
                        free_edges, rng);
                }
                apply_move(current, move);
                Evaluation candidate =
                    evaluate(current, cfg.target_degree, cfg.target_blockers);
                evaluated.fetch_add(1, std::memory_order_relaxed);
                apply_move(current, move);
                const int64_t candidate_energy =
                    dynamic_energy(candidate, weights);

                if (!chosen_set || candidate_energy < chosen_energy ||
                    (candidate_energy == chosen_energy &&
                     better(candidate, chosen_eval))) {
                    chosen = move;
                    chosen_eval = candidate;
                    chosen_energy = candidate_energy;
                    chosen_set = true;
                }
            }

            const int64_t delta = chosen_energy - current_energy;
            const double progress = static_cast<double>(step) / RESTART_STEPS;
            const double temperature = 18000.0 * (1.0 - progress) + 120.0;
            const double probability =
                delta <= 0 ? 1.0 : std::exp(-static_cast<double>(delta) / temperature);
            std::uniform_real_distribution<double> uniform(0.0, 1.0);
            const bool noisy_accept = (rng() % 1000) < 10;

            if (delta <= 0 || noisy_accept || uniform(rng) < probability) {
                apply_move(current, chosen);
                const bool improved =
                    chosen_energy < current_energy ||
                    (chosen_energy == current_energy &&
                     better(chosen_eval, current_eval));
                current_eval = chosen_eval;
                current_energy = chosen_energy;
                stagnation = improved ? 0 : stagnation + 1;
                publish_best(shared, current, current_eval, cfg, thread_id);
            } else {
                ++stagnation;
            }

            // NuWLS-style constraint weighting: a repeatedly violated vertex
            // gains influence until the walk is pushed out of the plateau.
            if (stagnation > 0 && stagnation % 400 == 0) {
                int offender = -1;
                for (int v = 0; v < N; ++v) {
                    if (current_eval.margin[v] > 0 &&
                        (offender < 0 ||
                         weights[v] * current_eval.margin[v] >
                             weights[offender] * current_eval.margin[offender])) {
                        offender = v;
                    }
                }
                if (offender >= 0) {
                    weights[offender] = std::min(64, weights[offender] + 1);
                    current_energy = dynamic_energy(current_eval, weights);
                }
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
    if (six != 7 || seven != 7) return false;

    for (const int degree : {7, 6}) {
        const int expected = binomial(13, degree - 1);
        int total = 0;
        std::vector<bool> seen(1u << 13, false);
        for (int bucket = 0; bucket < PARTITION_BUCKETS; ++bucket) {
            const auto patterns = build_zero_patterns(degree, bucket);
            if (patterns.empty()) return false;
            total += static_cast<int>(patterns.size());
            for (const uint16_t subset : patterns) {
                if (seen[subset]) return false;
                if (bit_count(subset) != degree - 1) return false;
                if (colex_rank(subset) % PARTITION_BUCKETS != bucket) return false;
                seen[subset] = true;
            }
        }
        if (total != expected) return false;
    }

    std::mt19937_64 rng(123456789ULL);
    Config cfg;
    cfg.target_degree = 7;
    cfg.target_blockers = 1;
    cfg.bucket = 0;
    const auto patterns = build_zero_patterns(7, 0);
    const auto free_edges = build_free_edges();
    for (int trial = 0; trial < 100; ++trial) {
        State state = random_state(rng, patterns);
        const Evaluation e = evaluate(state, 7, 1);
        if (!validate_tournament(state) || !in_partition(state, cfg)) return false;
        for (int v = 0; v < N; ++v) {
            if (e.margin[v] != 15 - 2 * e.degree[v] - e.blockers[v]) {
                return false;
            }
            int manual_extra = N;
            for (int x = 0; x < N; ++x) {
                if (x == v || !arc(state, x, v)) continue;
                int defect = 0;
                uint16_t bits = state.out[v];
                while (bits) {
                    const int u = first_bit(bits);
                    bits &= static_cast<uint16_t>(bits - 1);
                    defect += arc(state, u, x);
                }
                if (defect > 0) manual_extra = std::min(manual_extra, defect);
            }
            if (manual_extra != e.extra_blocker_defect[v]) return false;
        }
        const auto edge = free_edges[rng() % free_edges.size()];
        flip_edge(state, edge.first, edge.second);
        if (!in_partition(state, cfg)) return false;
    }
    return true;
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

    const bool witness =
        shared.initialized && is_witness(shared.state, shared.eval, cfg);
    const uint16_t subset = zero_subset(shared.state);
    const int rank = colex_rank(subset);
    const auto bucket_patterns =
        build_zero_patterns(cfg.target_degree, cfg.bucket);
    out << "{\n";
    out << "  \"campaign\": \"K16-PISA-v7-blocker-breakout-repair\",\n";
    out << "  \"platform\": \"github-cpu\",\n";
    out << "  \"status\": \"" << (witness ? "WITNESS" : "NO_WITNESS") << "\",\n";
    out << "  \"shard\": " << cfg.shard << ",\n";
    out << "  \"strategy\": \""
        << (cfg.target_degree == 7 ? "d7_b1" : "d6_b3")
        << "_bucket_" << std::setw(2) << std::setfill('0') << cfg.bucket
        << "_dynamic_blocker_repair";
    out << "\",\n";
    out << std::setfill(' ');
    out << "  \"partition_scheme\": "
        << "\"zero-out-neighbour-colex-rank-mod-32\",\n";
    out << "  \"partition_bucket\": " << cfg.bucket << ",\n";
    out << "  \"partition_bucket_count\": " << PARTITION_BUCKETS << ",\n";
    out << "  \"partition_pattern_count\": " << bucket_patterns.size() << ",\n";
    out << "  \"zero_out_subset\": " << subset << ",\n";
    out << "  \"zero_out_rank\": " << rank << ",\n";
    out << "  \"partition_valid\": "
        << (in_partition(shared.state, cfg) ? "true" : "false") << ",\n";
    out << "  \"target_degree\": " << cfg.target_degree << ",\n";
    out << "  \"target_blockers\": " << cfg.target_blockers << ",\n";
    out << "  \"threads\": " << cfg.threads << ",\n";
    out << "  \"wall_seconds\": " << std::fixed << std::setprecision(3)
        << wall_seconds << ",\n";
    out << "  \"states_evaluated\": " << states_evaluated << ",\n";
    out << "  \"repair_attempts\": "
        << repair_attempts.load(std::memory_order_relaxed) << ",\n";
    out << "  \"repair_states\": "
        << repair_states.load(std::memory_order_relaxed) << ",\n";
    out << "  \"elite_pool_size\": " << shared.pool.size() << ",\n";
    out << "  \"best_loss\": " << shared.eval.loss << ",\n";
    out << "  \"best_positive_defect_sum\": "
        << shared.eval.positive_defect_sum << ",\n";
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
    out << "  \"extra_blocker_defects\": "
        << json_array(shared.eval.extra_blocker_defect) << ",\n";
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

    if (cfg.shard < 0 || cfg.shard >= 64) {
        throw std::runtime_error("shard must be in [0,63]");
    }
    cfg.target_degree = cfg.shard < 32 ? 7 : 6;
    cfg.target_blockers = cfg.target_degree == 7 ? 1 : 3;
    cfg.bucket = cfg.shard % PARTITION_BUCKETS;
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
        const auto zero_patterns =
            build_zero_patterns(cfg.target_degree, cfg.bucket);
        if (free_edges.size() != 91) {
            throw std::runtime_error(
                "expected 91 mutable nonzero edges after fixing cycle and partition");
        }
        if (zero_patterns.empty()) {
            throw std::runtime_error("partition bucket has no zero-neighbour patterns");
        }

        SharedBest shared;
        std::vector<std::thread> workers;
        for (int t = 0; t < cfg.threads; ++t) {
            workers.emplace_back(
                worker, t, std::cref(cfg), deadline, std::ref(shared),
                std::cref(free_edges), std::cref(triples),
                std::cref(zero_patterns));
        }
        for (auto& thread : workers) thread.join();

        const double wall_seconds =
            std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
        write_json(cfg, shared, wall_seconds, evaluated.load());

        std::cout << "status="
                  << (shared.witness ? "WITNESS" : "NO_WITNESS")
                  << " shard=" << cfg.shard
                  << " branch=" << (cfg.target_degree == 7 ? "d7_b1" : "d6_b3")
                  << " bucket=" << cfg.bucket
                  << " loss=" << shared.eval.loss
                  << " defect=" << shared.eval.positive_defect_sum
                  << " elites=" << shared.pool.size()
                  << " repairs=" << repair_attempts.load()
                  << " states=" << evaluated.load()
                  << " seconds=" << std::fixed << std::setprecision(2)
                  << wall_seconds << "\n";
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "ERROR: " << error.what() << "\n";
        return 2;
    }
}
