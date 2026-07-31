#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef _OPENMP
#include <omp.h>
#endif

namespace {

constexpr int kTargetWeight = 16;
constexpr int kMaxH = 9;

struct AuditRow {
    int h = 0;
    std::uint64_t catalogue_tournaments = 0;
    std::uint64_t strong_tournaments = 0;
    std::uint64_t weight_vectors = 0;
    std::uint64_t tested_pairs = 0;
    std::uint64_t feasible_pairs = 0;
    double seconds = 0.0;
};

using Weight = std::array<std::uint8_t, kMaxH>;

std::vector<Weight> positive_compositions(int total, int parts) {
    std::vector<Weight> result;
    Weight current{};

    const auto rec = [&](const auto& self, int index, int remaining) -> void {
        if (index == parts - 1) {
            if (remaining >= 1) {
                current[index] = static_cast<std::uint8_t>(remaining);
                result.push_back(current);
            }
            return;
        }
        const int remaining_parts = parts - index - 1;
        for (int value = 1; value <= remaining - remaining_parts; ++value) {
            current[index] = static_cast<std::uint8_t>(value);
            self(self, index + 1, remaining - value);
        }
    };

    rec(rec, 0, total);
    return result;
}

std::array<std::uint16_t, kMaxH> decode_tournament(
    const std::string& bits,
    int h
) {
    const int expected = h * (h - 1) / 2;
    if (static_cast<int>(bits.size()) != expected) {
        throw std::runtime_error(
            "bad tournament line length for h=" + std::to_string(h)
        );
    }

    std::array<std::uint16_t, kMaxH> out{};
    int k = 0;
    for (int i = 0; i < h; ++i) {
        for (int j = i + 1; j < h; ++j) {
            const char bit = bits[k++];
            if (bit == '1') {
                out[i] |= static_cast<std::uint16_t>(1U << j);
            } else if (bit == '0') {
                out[j] |= static_cast<std::uint16_t>(1U << i);
            } else {
                throw std::runtime_error("catalogue contains a non-bit");
            }
        }
    }
    return out;
}

bool strongly_connected(
    const std::array<std::uint16_t, kMaxH>& out,
    int h
) {
    const std::uint16_t all =
        static_cast<std::uint16_t>((1U << h) - 1U);

    const auto reaches_all = [&](bool reverse) {
        std::uint16_t seen = 1U;
        std::uint16_t frontier = 1U;
        while (frontier != 0U) {
            std::uint16_t next = 0U;
            for (int u = 0; u < h; ++u) {
                if ((frontier & (1U << u)) == 0U) {
                    continue;
                }
                if (!reverse) {
                    next |= out[u];
                } else {
                    for (int v = 0; v < h; ++v) {
                        if ((out[v] & (1U << u)) != 0U) {
                            next |= static_cast<std::uint16_t>(1U << v);
                        }
                    }
                }
            }
            next &= static_cast<std::uint16_t>(~seen);
            seen |= next;
            frontier = next;
        }
        return seen == all;
    };

    return reaches_all(false) && reaches_all(true);
}

std::array<std::array<std::int8_t, kMaxH>, kMaxH>
weighted_margin_matrix(
    const std::array<std::uint16_t, kMaxH>& out,
    int h
) {
    std::array<std::array<std::int8_t, kMaxH>, kMaxH> matrix{};

    for (int v = 0; v < h; ++v) {
        std::uint16_t second = 0U;
        for (int u = 0; u < h; ++u) {
            if ((out[v] & (1U << u)) != 0U) {
                second |= out[u];
            }
        }
        second &= static_cast<std::uint16_t>(~out[v]);
        second &= static_cast<std::uint16_t>(~(1U << v));

        for (int x = 0; x < h; ++x) {
            if ((out[v] & (1U << x)) != 0U) {
                matrix[v][x] = -1;
            } else if ((second & (1U << x)) != 0U) {
                matrix[v][x] = 1;
            }
        }
    }
    return matrix;
}

bool weighted_pisa_feasible(
    const std::array<std::array<std::int8_t, kMaxH>, kMaxH>& matrix,
    const Weight& weight,
    int h
) {
    for (int row = 0; row < h; ++row) {
        int margin = 0;
        for (int col = 0; col < h; ++col) {
            margin +=
                static_cast<int>(matrix[row][col]) *
                static_cast<int>(weight[col]);
        }
        if (margin > 0) {
            return false;
        }
    }
    return true;
}

std::vector<std::string> read_catalogue(
    const std::string& path
) {
    std::ifstream input(path);
    if (!input) {
        throw std::runtime_error("cannot open catalogue: " + path);
    }
    std::vector<std::string> lines;
    std::string line;
    while (std::getline(input, line)) {
        if (!line.empty() && line.back() == '\r') {
            line.pop_back();
        }
        if (!line.empty()) {
            lines.push_back(line);
        }
    }
    return lines;
}

AuditRow audit_h(
    const std::string& data_dir,
    int h
) {
    const auto started = std::chrono::steady_clock::now();
    const auto lines =
        read_catalogue(data_dir + "/tourn" + std::to_string(h) + ".txt");
    const auto weights = positive_compositions(kTargetWeight, h);

    std::uint64_t strong_count = 0;
    std::uint64_t tested_pairs = 0;
    std::uint64_t feasible_pairs = 0;

#pragma omp parallel for schedule(dynamic, 32) \
    reduction(+:strong_count,tested_pairs,feasible_pairs)
    for (std::int64_t index = 0;
         index < static_cast<std::int64_t>(lines.size());
         ++index) {
        const auto out = decode_tournament(lines[index], h);
        if (!strongly_connected(out, h)) {
            continue;
        }
        ++strong_count;
        tested_pairs += weights.size();
        const auto matrix = weighted_margin_matrix(out, h);
        for (const auto& weight : weights) {
            if (weighted_pisa_feasible(matrix, weight, h)) {
                ++feasible_pairs;
            }
        }
    }

    const auto finished = std::chrono::steady_clock::now();
    const double seconds =
        std::chrono::duration<double>(finished - started).count();

    return AuditRow{
        h,
        static_cast<std::uint64_t>(lines.size()),
        strong_count,
        static_cast<std::uint64_t>(weights.size()),
        tested_pairs,
        feasible_pairs,
        seconds,
    };
}

void write_json(
    const std::string& path,
    const std::vector<AuditRow>& rows
) {
    std::ofstream output(path);
    if (!output) {
        throw std::runtime_error("cannot write result: " + path);
    }

    output << "{\n";
#ifdef _OPENMP
    output << "  \"openmp_threads\": " << omp_get_max_threads() << ",\n";
#else
    output << "  \"openmp_threads\": 1,\n";
#endif
    output << "  \"target_weight\": " << kTargetWeight << ",\n";
    output << "  \"rows\": [\n";
    for (std::size_t i = 0; i < rows.size(); ++i) {
        const auto& row = rows[i];
        output << "    {\n"
               << "      \"h\": " << row.h << ",\n"
               << "      \"catalogue_tournaments\": "
               << row.catalogue_tournaments << ",\n"
               << "      \"strong_tournaments\": "
               << row.strong_tournaments << ",\n"
               << "      \"weight_vectors\": "
               << row.weight_vectors << ",\n"
               << "      \"tested_pairs\": "
               << row.tested_pairs << ",\n"
               << "      \"feasible_pairs\": "
               << row.feasible_pairs << ",\n"
               << "      \"seconds\": " << row.seconds << "\n"
               << "    }";
        if (i + 1 != rows.size()) {
            output << ",";
        }
        output << "\n";
    }
    output << "  ]\n}\n";
}

}  // namespace

int main(int argc, char** argv) {
    if (argc != 3) {
        std::cerr
            << "usage: weighted_quotient_audit DATA_DIR OUTPUT_JSON\n";
        return 2;
    }

    try {
        std::vector<AuditRow> rows;
        for (int h = 3; h <= 9; ++h) {
            const auto row = audit_h(argv[1], h);
            rows.push_back(row);
            std::cout
                << "h=" << h
                << " catalogue=" << row.catalogue_tournaments
                << " strong=" << row.strong_tournaments
                << " weights=" << row.weight_vectors
                << " tested=" << row.tested_pairs
                << " feasible=" << row.feasible_pairs
                << " seconds=" << row.seconds
                << std::endl;
        }
        write_json(argv[2], rows);
    } catch (const std::exception& error) {
        std::cerr << "AUDIT_ERROR: " << error.what() << "\n";
        return 1;
    }
    return 0;
}
