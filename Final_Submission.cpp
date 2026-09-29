#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

constexpr int MAX_TURN = 200;
constexpr int START_GOLD = 500;
constexpr int START_WARRIORS = 3;
constexpr int MOVE_COST = 10;
constexpr int TRAIN_COST = 120;
constexpr int WORK_INCOME = 15;
constexpr int UPKEEP_PER_WARRIOR = 2;
constexpr int HQ_MAX_LEVEL = 5;
constexpr int BASE_MAX_LEVEL = 3;
constexpr int HQ_HEAL_COST = 1000;
constexpr int BASE_HEAL_COST = 500;
constexpr int TARGET_BASE_COUNT = 10;
constexpr int RALLY_ATTACK_COUNT = 20;

struct HqLevelEntry {
  int upgrade_cost;
  int warrior_hp;
  int hp;
  int turret;
  int train_cap;
  int work_cap;
};

struct BaseLevelEntry {
  int cost;
  int hp;
  int turret;
  int work_cap;
};

constexpr HqLevelEntry HQ_LEVELS[HQ_MAX_LEVEL + 1] = {
    {0, 0, 0, 0, 0, 0},     {0, 4, 10, 1, 1, 1},
    {600, 5, 15, 2, 1, 2},  {1200, 6, 20, 2, 2, 3},
    {2400, 7, 25, 3, 2, 4}, {3600, 8, 30, 3, 3, 5},
};

constexpr BaseLevelEntry BASE_LEVELS[BASE_MAX_LEVEL + 1] = {
    {0, 0, 0, 0},
    {300, 6, 1, 1},
    {600, 12, 1, 2},
    {1000, 18, 2, 3},
};

static int g_hq_assault_rally_region = -1;
static bool g_hq_assault_committed = false;
static std::vector<int> g_large_saved_goal_by_warrior;
static std::vector<int> g_idle_base_surplus_turns_by_warrior;

enum class Side : int { LEFT = 0, RIGHT = 1 };
enum class BType : int { HQ, BASE };
enum class WState : int { STATIONARY, MOVING };

inline Side opposite(Side s) {
  return s == Side::LEFT ? Side::RIGHT : Side::LEFT;
}
inline char side_char(Side s) { return s == Side::LEFT ? 'A' : 'B'; }
inline Side parse_side_char(char c) {
  return c == 'A' ? Side::LEFT : Side::RIGHT;
}

struct WarriorId {
  Side side = Side::LEFT;
  int num = 0;
  bool operator==(const WarriorId &o) const {
    return side == o.side && num == o.num;
  }
  bool operator<(const WarriorId &o) const {
    if (side != o.side)
      return static_cast<int>(side) < static_cast<int>(o.side);
    return num < o.num;
  }
};

struct Warrior {
  WarriorId id;
  int region = 0;
  int hp = 0;
  WState state = WState::STATIONARY;
  int target = 0;
};

struct Building {
  int region = 0;
  Side side = Side::LEFT;
  BType type = BType::HQ;
  int level = 1;
  int hp = 10;

  int current_hp() const {
    return type == BType::HQ ? HQ_LEVELS[level].hp : BASE_LEVELS[level].hp;
  }
  int work_cap() const {
    return type == BType::HQ ? HQ_LEVELS[level].work_cap
                             : BASE_LEVELS[level].work_cap;
  }
};

struct GameMap {
  int N = 0, K = 0;
  std::vector<long long> x, y;
  std::vector<int> strongholds;
  std::vector<std::vector<int>> adj;

  Side my_side = Side::LEFT;
  int my_hq = 0;
  int opp_hq = 0;
};

constexpr bool FORCE_WARM_STRATEGY_ALL_MAPS = true;

static bool large_strategy_active(const GameMap &M) {
  return M.N >= 90 && !FORCE_WARM_STRATEGY_ALL_MAPS;
}

static bool forced_warm_large_map(const GameMap &M) {
  return FORCE_WARM_STRATEGY_ALL_MAPS && M.N >= 90;
}

static int warm_opening_base_goal(const GameMap &M) {
  if (!forced_warm_large_map(M))
    return 2;
  return M.N <= 100 ? 3 : 4;
}

static int warm_rally_min_attackers(const GameMap &M) {
  if (!forced_warm_large_map(M))
    return 5;
  return 7;
}

struct GameState {
  int gold = START_GOLD;
  int my_countdown = 5;
  int opp_countdown = 5;
  std::vector<Warrior> warriors;
  std::vector<Building> buildings;
};

struct Actions {
  int train_n = 0;
  std::vector<std::pair<WarriorId, int>> moves;
  std::vector<int> upgrades;
};

static std::string readln() {
  std::string s;
  if (!std::getline(std::cin, s))
    std::exit(0);
  return s;
}

static std::vector<std::string> tokens(const std::string &s) {
  std::vector<std::string> out;
  std::istringstream is(s);
  for (std::string t; is >> t;)
    out.push_back(t);
  return out;
}

static WarriorId parse_warrior(const std::string &tok) {
  assert(!tok.empty() && (tok[0] == 'A' || tok[0] == 'B'));
  WarriorId id;
  id.side = parse_side_char(tok[0]);
  id.num = std::stoi(tok.substr(1));
  return id;
}

static std::string format_warrior(WarriorId id) {
  std::string s;
  s.push_back(side_char(id.side));
  s += std::to_string(id.num);
  return s;
}

static int hq_of(const GameMap &M, Side s) {
  return (s == Side::LEFT) ? 0 : M.N - 1;
}

static Building make_base(int region, Side s) {
  return Building{region, s, BType::BASE, 1, BASE_LEVELS[1].hp};
}

static void apply_upgrade(Building &b) {
  b.level += 1;
  b.hp = b.current_hp();
}

static int max_level(const Building &b) {
  return b.type == BType::HQ ? HQ_MAX_LEVEL : BASE_MAX_LEVEL;
}

static int upgrade_cost(const Building &b) {
  if (b.type == BType::HQ) {
    if (b.level >= HQ_MAX_LEVEL)
      return HQ_HEAL_COST;
    return HQ_LEVELS[b.level + 1].upgrade_cost;
  }
  if (b.level >= BASE_MAX_LEVEL)
    return BASE_HEAL_COST;
  return BASE_LEVELS[b.level + 1].cost;
}

static void parse_init(GameMap &M, GameState &S) {
  {
    auto t = tokens(readln());
    assert(t.size() >= 2 && t[0] == "READY");
    M.my_side = (t[1] == "LEFT") ? Side::LEFT : Side::RIGHT;
  }
  {
    auto t = tokens(readln());
    M.N = std::stoi(t.at(0));
    M.K = std::stoi(t.at(1));
  }
  M.x.assign(M.N, 0);
  M.y.assign(M.N, 0);
  {
    auto t = tokens(readln());
    for (int i = 0; i < M.N; ++i)
      M.x[i] = std::stoll(t.at(i));
  }
  {
    auto t = tokens(readln());
    for (int i = 0; i < M.N; ++i)
      M.y[i] = std::stoll(t.at(i));
  }
  {
    auto t = tokens(readln());
    M.strongholds.clear();
    M.strongholds.reserve(t.size());
    for (const auto &s : t)
      M.strongholds.push_back(std::stoi(s));
    std::sort(M.strongholds.begin(), M.strongholds.end());
  }
  M.adj.assign(M.N, {});
  for (int r = 0; r < M.N; ++r) {
    auto t = tokens(readln());
    int deg = std::stoi(t.at(0));
    auto &nb = M.adj[r];
    nb.reserve(deg);
    for (int j = 0; j < deg; ++j)
      nb.push_back(std::stoi(t.at(1 + j)));
    std::sort(nb.begin(), nb.end());
  }

  M.my_hq = hq_of(M, M.my_side);
  M.opp_hq = hq_of(M, opposite(M.my_side));

  S = GameState{};
  S.gold = START_GOLD;
  Side opp = opposite(M.my_side);
  for (int sfx = 1; sfx <= START_WARRIORS; ++sfx) {
    S.warriors.push_back(Warrior{.id = WarriorId{M.my_side, sfx},
                                 .region = M.my_hq,
                                 .hp = HQ_LEVELS[1].warrior_hp});
    S.warriors.push_back(Warrior{.id = WarriorId{opp, sfx},
                                 .region = M.opp_hq,
                                 .hp = HQ_LEVELS[1].warrior_hp});
  }
  S.buildings.push_back(Building{hq_of(M, Side::LEFT), Side::LEFT, BType::HQ,
                                 1, HQ_LEVELS[1].hp});
  S.buildings.push_back(Building{hq_of(M, Side::RIGHT), Side::RIGHT,
                                 BType::HQ, 1, HQ_LEVELS[1].hp});

  std::cout << "OK" << std::endl;
}

static bool read_turn_start(int &turn_index) {
  std::string line = readln();
  if (line == "FINISH")
    return false;
  auto t = tokens(line);
  assert(!t.empty() && t[0] == "START");
  turn_index = std::stoi(t.at(2));
  return true;
}

static Building *find_building(GameState &S, int region) {
  for (auto &b : S.buildings)
    if (b.region == region)
      return &b;
  return nullptr;
}

static const Building *find_building(const GameState &S, int region) {
  for (const auto &b : S.buildings)
    if (b.region == region)
      return &b;
  return nullptr;
}

static Warrior *find_warrior(GameState &S, WarriorId id) {
  for (auto &w : S.warriors)
    if (w.id == id)
      return &w;
  return nullptr;
}

static void read_turn_result(GameState &S, const GameMap &M,
                             const Actions &submitted) {
  for (int region : submitted.upgrades) {
    Building *b = find_building(S, region);
    if (b == nullptr) {
      S.gold -= BASE_LEVELS[1].cost;
      S.buildings.push_back(make_base(region, M.my_side));
    } else {
      if (b->level >= max_level(*b)) {
        int cost = (b->type == BType::HQ) ? HQ_HEAL_COST : BASE_HEAL_COST;
        S.gold -= cost;
        b->hp = b->current_hp();
      } else {
        S.gold -= upgrade_cost(*b);
        apply_upgrade(*b);
      }
    }
  }

  for (const auto &move_plan : submitted.moves) {
    const WarriorId &id = move_plan.first;
    int target = move_plan.second;
    Building *b = find_building(S, target);
    int cost = (b != nullptr && b->side == M.my_side) ? 0 : MOVE_COST;
    S.gold -= cost;
    if (Warrior *w = find_warrior(S, id)) {
      w->state = WState::MOVING;
      w->target = target;
    }
  }

  S.gold -= TRAIN_COST * submitted.train_n;

  {
    std::string line = readln();
    if (line == "FINISH")
      std::exit(0);
    auto t = tokens(line);
    assert(!t.empty() && t[0] == "TURN");
  }
  {
    auto t = tokens(readln());
    S.my_countdown = std::stoi(t.at(2));
    S.opp_countdown = std::stoi(t.at(4));
  }
  {
    auto t = tokens(readln());
    int n = std::stoi(t.at(1));
    for (int i = 0; i < n; ++i) {
      auto r = tokens(readln());
      Side s = parse_side_char(r.at(0)[0]);
      int region = std::stoi(r.at(1));
      Building *b = find_building(S, region);
      if (b == nullptr) {
        S.buildings.push_back(make_base(region, s));
      } else if (b->side != M.my_side) {
        if (b->level >= max_level(*b)) {
          b->hp = b->current_hp();
        } else {
          apply_upgrade(*b);
        }
      }
    }
  }
  {
    auto t = tokens(readln());
    int n = std::stoi(t.at(1));
    if (n > 0) {
      auto ids = tokens(readln());
      for (int i = 0; i < n; ++i) {
        WarriorId id = parse_warrior(ids.at(i));
        int hq_region = hq_of(M, id.side);
        Building *hq_b = find_building(S, hq_region);
        int hq_level = (hq_b != nullptr) ? hq_b->level : 1;
        S.warriors.push_back(Warrior{.id = id,
                                     .region = hq_region,
                                     .hp = HQ_LEVELS[hq_level].warrior_hp});
      }
    }
  }
  {
    auto t = tokens(readln());
    int n = std::stoi(t.at(1));
    for (int i = 0; i < n; ++i) {
      auto r = tokens(readln());
      WarriorId id = parse_warrior(r.at(0));
      int region = std::stoi(r.at(1));
      if (Warrior *w = find_warrior(S, id)) {
        w->region = region;
        if (id.side == M.my_side && w->state == WState::MOVING &&
            w->region == w->target) {
          w->state = WState::STATIONARY;
        }
      }
    }
  }
  {
    auto t = tokens(readln());
    int n = std::stoi(t.at(1));
    for (int i = 0; i < n; ++i) {
      auto r = tokens(readln());
      WarriorId id = parse_warrior(r.at(1));
      int damage = std::stoi(r.at(2));
      if (Warrior *w = find_warrior(S, id))
        w->hp -= damage;
    }
    S.warriors.erase(std::remove_if(S.warriors.begin(), S.warriors.end(),
                                    [](const Warrior &w) { return w.hp <= 0; }),
                     S.warriors.end());
  }
  {
    auto t = tokens(readln());
    int n = std::stoi(t.at(1));
    for (int i = 0; i < n; ++i) {
      auto r = tokens(readln());
      int region = std::stoi(r.at(1));
      int damage = std::stoi(r.at(2));
      if (Building *b = find_building(S, region))
        b->hp -= damage;
    }
    S.buildings.erase(
        std::remove_if(S.buildings.begin(), S.buildings.end(),
                       [](const Building &b) { return b.hp <= 0; }),
        S.buildings.end());
  }
  (void)readln();

  int income = 0;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    int count = 0;
    for (const auto &w : S.warriors) {
      if (w.id.side == M.my_side && w.region == b.region)
        ++count;
    }
    income += WORK_INCOME * std::min(count, b.work_cap());
  }
  S.gold += income;

  int alive = 0;
  for (const auto &w : S.warriors)
    if (w.id.side == M.my_side)
      ++alive;
  S.gold = std::max(0, S.gold - UPKEEP_PER_WARRIOR * alive);
}

struct Paths {
  std::vector<std::vector<double>> dist;
  std::vector<std::vector<int>> nxt;
  std::vector<std::vector<int>> hops;
};

static double euclid_ceil(const GameMap &M, int u, int v) {
  double dx = static_cast<double>(M.x[u] - M.x[v]);
  double dy = static_cast<double>(M.y[u] - M.y[v]);
  return std::ceil(std::sqrt(dx * dx + dy * dy));
}

static Paths calculate_paths(const GameMap &M) {
  const double INF = std::numeric_limits<double>::infinity();
  Paths P;
  P.dist.assign(M.N, std::vector<double>(M.N, INF));
  P.nxt.assign(M.N, std::vector<int>(M.N, -1));
  P.hops.assign(M.N, std::vector<int>(M.N, M.N + 1));

  for (int i = 0; i < M.N; ++i) {
    P.dist[i][i] = 0.0;
    P.nxt[i][i] = i;
    P.hops[i][i] = 0;
  }
  for (int u = 0; u < M.N; ++u) {
    for (int v : M.adj[u]) {
      double w = euclid_ceil(M, u, v);
      if (w < P.dist[u][v])
        P.dist[u][v] = w;
      P.hops[u][v] = 1;
    }
  }

  for (int k = 0; k < M.N; ++k) {
    for (int u = 0; u < M.N; ++u) {
      if (P.dist[u][k] == INF)
        continue;
      for (int v = 0; v < M.N; ++v) {
        double cand = P.dist[u][k] + P.dist[k][v];
        if (cand < P.dist[u][v])
          P.dist[u][v] = cand;
        if (P.hops[u][k] + P.hops[k][v] < P.hops[u][v])
          P.hops[u][v] = P.hops[u][k] + P.hops[k][v];
      }
    }
  }

  for (int u = 0; u < M.N; ++u) {
    for (int v = 0; v < M.N; ++v) {
      if (u == v || P.dist[u][v] == INF)
        continue;
      double best_score = INF;
      for (int nb : M.adj[u]) {
        if (P.dist[nb][v] == INF)
          continue;
        double score = euclid_ceil(M, u, nb) + P.dist[nb][v];
        if (score < best_score) {
          best_score = score;
          P.nxt[u][v] = nb;
        }
      }
    }
  }
  return P;
}

[[maybe_unused]] static int next_step(const Paths &P, int u, int v) {
  return P.nxt[u][v];
}

static void emit_command() { std::cout << "COMMAND\n"; }

static void emit_actions(const Actions &a) {
  for (const auto &move_plan : a.moves) {
    const WarriorId &id = move_plan.first;
    int target = move_plan.second;
    std::cout << "MOVE " << format_warrior(id) << ' ' << target << '\n';
  }
  for (int r : a.upgrades) {
    std::cout << "UPGRADE " << r << '\n';
  }
  if (a.train_n > 0) {
    std::cout << "TRAIN " << a.train_n << '\n';
  }
}

static void emit_end() { std::cout << "END" << std::endl; }

static bool is_stronghold(const GameMap &M, int region) {
  return std::binary_search(M.strongholds.begin(), M.strongholds.end(), region);
}

static const Building *my_hq_building(const GameState &S, const GameMap &M) {
  const Building *b = find_building(S, M.my_hq);
  return (b != nullptr && b->side == M.my_side && b->type == BType::HQ) ? b
                                                                        : nullptr;
}

static int count_warriors_at(const GameState &S, int region, Side side) {
  int count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side == side && w.region == region)
      ++count;
  }
  return count;
}

static int count_my_warriors_at(const GameState &S, int region,
                                const GameMap &M) {
  return count_warriors_at(S, region, M.my_side);
}

static int count_enemy_warriors_at(const GameState &S, int region,
                                   const GameMap &M) {
  return count_warriors_at(S, region, opposite(M.my_side));
}

static int count_my_alive(const GameState &S, const GameMap &M) {
  int count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side)
      ++count;
  }
  return count;
}

[[maybe_unused]] static int estimate_income(const GameState &S,
                                            const GameMap &M) {
  int income = 0;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    int workers = count_my_warriors_at(S, b.region, M);
    income += WORK_INCOME * std::min(workers, b.work_cap());
  }
  return income;
}

static int move_cost_to(const GameState &S, const GameMap &M, int target) {
  const Building *b = find_building(S, target);
  return (b != nullptr && b->side == M.my_side) ? 0 : MOVE_COST;
}

static bool warrior_already_planned(const Actions &a, WarriorId id) {
  for (const auto &move_plan : a.moves) {
    const WarriorId &moved_id = move_plan.first;
    if (moved_id == id)
      return true;
  }
  return false;
}

[[maybe_unused]] static int count_my_buildings(const GameState &S,
                                               const GameMap &M) {
  int count = 0;
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side)
      ++count;
  }
  return count;
}

static int count_my_bases(const GameState &S, const GameMap &M) {
  int count = 0;
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side && b.type == BType::BASE)
      ++count;
  }
  return count;
}

static int count_enemy_bases(const GameState &S, const GameMap &M) {
  int count = 0;
  Side enemy = opposite(M.my_side);
  for (const auto &b : S.buildings) {
    if (b.side == enemy && b.type == BType::BASE)
      ++count;
  }
  return count;
}

[[maybe_unused]] static int count_my_stationary(const GameState &S,
                                                const GameMap &M) {
  int count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::STATIONARY)
      ++count;
  }
  return count;
}

[[maybe_unused]] static int count_my_stationary_at(const GameState &S,
                                                   int region,
                                                   const GameMap &M) {
  int count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::STATIONARY &&
        w.region == region) {
      ++count;
    }
  }
  return count;
}

static bool has_worker_heading_to(const GameState &S, const GameMap &M,
                                  int target) {
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::MOVING &&
        w.target == target) {
      return true;
    }
  }
  return false;
}

static int planned_moves_from_region(const Actions &a, const GameState &S,
                                     int region) {
  int count = 0;
  for (const auto &move_plan : a.moves) {
    const WarriorId &id = move_plan.first;
    for (const auto &w : S.warriors) {
      if (w.id == id && w.region == region) {
        ++count;
        break;
      }
    }
  }
  return count;
}

static int planned_moves_to_region(const Actions &a, int region) {
  int count = 0;
  for (const auto &move_plan : a.moves) {
    int target = move_plan.second;
    if (target == region)
      ++count;
  }
  return count;
}

static bool is_region_safe_for_build(const GameState &S, const GameMap &M,
                                     int region) {
  return count_my_warriors_at(S, region, M) > 0 &&
         count_enemy_warriors_at(S, region, M) == 0;
}

static int planned_upgrade_cost(const GameState &S, const GameMap &M,
                                int region) {
  const Building *b = find_building(S, region);
  if (b == nullptr)
    return is_stronghold(M, region) ? BASE_LEVELS[1].cost
                                    : std::numeric_limits<int>::max() / 4;
  if (b->side != M.my_side)
    return std::numeric_limits<int>::max() / 4;
  return upgrade_cost(*b);
}

static bool can_upgrade_region(const GameState &S, const GameMap &M, int region,
                               const std::set<int> &used_upgrades,
                               int planned_gold) {
  if (used_upgrades.count(region))
    return false;
  if (!is_region_safe_for_build(S, M, region))
    return false;
  const Building *b = find_building(S, region);
  if (b == nullptr && !is_stronghold(M, region))
    return false;
  if (b != nullptr && b->side != M.my_side)
    return false;
  if (b != nullptr && b->level >= max_level(*b) && b->hp >= b->current_hp())
    return false;
  return planned_upgrade_cost(S, M, region) <= planned_gold;
}

static bool can_build_base(const GameState &S, const GameMap &M, int region,
                           const std::set<int> &used_upgrades,
                           int planned_gold, int planned_own_buildings) {
  if (used_upgrades.count(region))
    return false;
  if (planned_own_buildings >= TARGET_BASE_COUNT)
    return false;
  if (!is_stronghold(M, region))
    return false;
  if (find_building(S, region) != nullptr)
    return false;
  if (!is_region_safe_for_build(S, M, region))
    return false;
  return BASE_LEVELS[1].cost <= planned_gold;
}

static bool add_upgrade_if_legal(const GameState &S, const GameMap &M,
                                 Actions &a, std::set<int> &used_upgrades,
                                 int &planned_gold, int region) {
  if (!can_upgrade_region(S, M, region, used_upgrades, planned_gold))
    return false;
  int cost = planned_upgrade_cost(S, M, region);
  a.upgrades.push_back(region);
  used_upgrades.insert(region);
  planned_gold -= cost;
  return true;
}

static bool add_base_build(const GameState &S, const GameMap &M, Actions &a,
                           std::set<int> &used_upgrades, int &planned_gold,
                           int &planned_own_buildings, int region) {
  if (!can_build_base(S, M, region, used_upgrades, planned_gold,
                      planned_own_buildings)) {
    return false;
  }
  a.upgrades.push_back(region);
  used_upgrades.insert(region);
  planned_gold -= BASE_LEVELS[1].cost;
  ++planned_own_buildings;
  return true;
}

static int reserve_need_at_region(const GameState &S, const GameMap &M,
                                  int region) {
  const Building *b = find_building(S, region);
  if (b == nullptr || b->side != M.my_side)
    return 0;
  if (b->type == BType::HQ)
    return std::max(1, std::min(b->work_cap(),
                                count_my_stationary_at(S, region, M)));
  if (large_strategy_active(M))
    return std::min(b->work_cap(), count_my_stationary_at(S, region, M));
  return std::min(1, count_my_stationary_at(S, region, M));
}

static bool is_committed_hq_assault_warrior(const Warrior &w,
                                            const GameMap &M) {
  if (w.id.side != M.my_side)
    return false;
  return (w.state == WState::MOVING && w.target == M.opp_hq) ||
         w.region == M.opp_hq;
}

static bool is_front_half_region_for_my_side(const GameMap &M, int region) {
  int center = M.N / 2;
  if (M.my_side == Side::LEFT)
    return region >= center;
  return region <= center;
}

static bool would_pull_forward_pressure_back(const GameMap &M, const Paths &P,
                                             int source, int target) {
  if (!is_front_half_region_for_my_side(M, source))
    return false;
  if (target == M.opp_hq)
    return false;
  if (is_front_half_region_for_my_side(M, target) &&
      P.hops[target][M.opp_hq] <= P.hops[source][M.opp_hq] + 1)
    return false;
  return P.hops[target][M.opp_hq] > P.hops[source][M.opp_hq] + 1;
}

static bool should_keep_attacking_under_emergency(const Warrior &w,
                                                  const GameMap &M) {
  if (is_committed_hq_assault_warrior(w, M))
    return true;
  if (M.N <= 56)
    return false;
  return w.id.side == M.my_side && is_front_half_region_for_my_side(M, w.region);
}

static bool should_recall_for_emergency(const Warrior &w, const GameMap &M) {
  return w.id.side == M.my_side &&
         !should_keep_attacking_under_emergency(w, M);
}

static bool can_move_non_emergency(const GameState &S, const GameMap &M,
                                   const Actions &a, const Warrior &w) {
  if (w.id.side != M.my_side || w.state != WState::STATIONARY)
    return false;
  if (warrior_already_planned(a, w.id))
    return false;

  int count = count_my_stationary_at(S, w.region, M);
  int leaving = planned_moves_from_region(a, S, w.region);
  return count - leaving > reserve_need_at_region(S, M, w.region);
}

static int large_base_staff_need(const Building &b) {
  if (b.type != BType::BASE)
    return 0;
  return std::max(1, std::min(b.level, b.work_cap()));
}

static int base_attack_staff_need(const Building &b) {
  if (b.type != BType::BASE)
    return 0;
  return std::max(1, std::min(b.level, b.work_cap()));
}

static int building_attack_staff_need(const Building &b) {
  return std::max(1, std::min(b.level, b.work_cap()));
}

static bool can_leave_large_base_strict(const GameState &S, const GameMap &M,
                                        const Actions &a, int region) {
  if (!large_strategy_active(M))
    return true;
  const Building *b = find_building(S, region);
  if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
    return true;
  int after_departures =
      count_my_stationary_at(S, region, M) - planned_moves_from_region(a, S, region);
  return after_departures > large_base_staff_need(*b);
}

static bool is_own_side_region(const GameMap &M, const Paths &P, int region) {
  return P.dist[M.my_hq][region] <= P.dist[M.opp_hq][region];
}

static int enemy_near_region(const GameState &S, const GameMap &M,
                             const Paths &P, int region, int radius) {
  int count = 0;
  Side enemy = opposite(M.my_side);
  for (const auto &w : S.warriors) {
    if (w.id.side == enemy && P.hops[w.region][region] <= radius)
      ++count;
  }
  return count;
}

static void large_goal_memory_reset() { g_large_saved_goal_by_warrior.clear(); }

static void large_goal_memory_ensure(int num) {
  if (num < 0)
    return;
  if (static_cast<int>(g_large_saved_goal_by_warrior.size()) <= num)
    g_large_saved_goal_by_warrior.resize(num + 1, -1);
}

static void large_goal_remember(WarriorId id, int goal) {
  if (id.num <= 0)
    return;
  large_goal_memory_ensure(id.num);
  g_large_saved_goal_by_warrior[id.num] = goal;
}

static void large_goal_clear(WarriorId id) {
  if (id.num <= 0 ||
      static_cast<int>(g_large_saved_goal_by_warrior.size()) <= id.num) {
    return;
  }
  g_large_saved_goal_by_warrior[id.num] = -1;
}

static int large_goal_saved(WarriorId id) {
  if (id.num <= 0 ||
      static_cast<int>(g_large_saved_goal_by_warrior.size()) <= id.num) {
    return -1;
  }
  return g_large_saved_goal_by_warrior[id.num];
}

static bool large_final_goal_useful(const GameState &S, const GameMap &M,
                                    int goal) {
  if (goal < 0 || goal >= M.N)
    return false;
  if (goal == M.opp_hq)
    return true;
  const Building *b = find_building(S, goal);
  if (b != nullptr)
    return b->side != M.my_side;
  return is_stronghold(M, goal);
}

static int large_waypoint_or_target(const GameState &S, const GameMap &M,
                                    const Paths &P, int from,
                                    int final_target) {
  if (!large_strategy_active(M) || final_target < 0 || final_target >= M.N)
    return final_target;
  if (from == final_target || P.nxt[from][final_target] == -1)
    return final_target;
  const Building *final_building = find_building(S, final_target);
  if (final_building != nullptr && final_building->side == M.my_side)
    return final_target;
  int direct = P.hops[from][final_target];
  if (direct <= 3)
    return final_target;

  int best = -1;
  int best_detour = 1000000;
  int best_first_hops = 1000000;
  double best_dist = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    if (b.region == from || b.region == final_target)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    if (P.nxt[from][b.region] == -1 || P.nxt[b.region][final_target] == -1)
      continue;
    if (would_pull_forward_pressure_back(M, P, from, b.region))
      continue;
    int via = P.hops[from][b.region] + P.hops[b.region][final_target];
    int detour = via - direct;
    if (detour < 0 || detour > 2)
      continue;
    int first_hops = P.hops[from][b.region];
    double dist = P.dist[from][b.region];
    if (detour < best_detour ||
        (detour == best_detour && first_hops < best_first_hops) ||
        (detour == best_detour && first_hops == best_first_hops &&
         dist < best_dist)) {
      best = b.region;
      best_detour = detour;
      best_first_hops = first_hops;
      best_dist = dist;
    }
  }
  return best >= 0 ? best : final_target;
}

static bool add_move_with_large_waypoint(const GameState &S, const GameMap &M,
                                         const Paths &P, Actions &a,
                                         int &planned_gold, const Warrior &w,
                                         int final_target,
                                         bool update_saved_goal = true) {
  if (final_target < 0 || final_target >= M.N)
    return false;
  if (w.id.side != M.my_side || w.state != WState::STATIONARY)
    return false;
  if (warrior_already_planned(a, w.id))
    return false;
  if (!can_leave_large_base_strict(S, M, a, w.region))
    return false;
  int target = large_waypoint_or_target(S, M, P, w.region, final_target);
  int cost = move_cost_to(S, M, target);
  if (planned_gold < cost)
    return false;
  a.moves.emplace_back(w.id, target);
  planned_gold -= cost;
  if (large_strategy_active(M) && update_saved_goal) {
    if (target != final_target && large_final_goal_useful(S, M, final_target))
      large_goal_remember(w.id, final_target);
    else
      large_goal_clear(w.id);
  }
  return true;
}

static bool is_contested_region(const GameState &S, const GameMap &M,
                                const Paths &P, int region) {
  if (count_enemy_warriors_at(S, region, M) > 0)
    return true;
  if (enemy_near_region(S, M, P, region, 1) > 0)
    return true;
  double my_d = P.dist[M.my_hq][region];
  double opp_d = P.dist[M.opp_hq][region];
  double total = P.dist[M.my_hq][M.opp_hq];
  if (total > 0.0 && std::abs(my_d - opp_d) <= total * 0.15)
    return true;
  return !is_own_side_region(M, P, region);
}

static std::vector<int> sorted_expansion_targets(const GameState &S,
                                                 const GameMap &M,
                                                 const Paths &P) {
  std::vector<int> targets;
  for (int r : M.strongholds) {
    if (find_building(S, r) != nullptr)
      continue;
    if (count_enemy_warriors_at(S, r, M) > 0)
      continue;
    if (P.nxt[M.my_hq][r] == -1)
      continue;
    if (!is_own_side_region(M, P, r) && count_my_bases(S, M) < 2)
      continue;
    targets.push_back(r);
  }
  std::sort(targets.begin(), targets.end(), [&](int a, int b) {
    auto score = [&](int r) {
      int nearest_building_hops = M.N + 1;
      for (const auto &bd : S.buildings) {
        if (bd.side == M.my_side)
          nearest_building_hops = std::min(nearest_building_hops, P.hops[bd.region][r]);
      }
      int center_risk = is_contested_region(S, M, P, r) ? 80 : 0;
      int enemy_penalty = enemy_near_region(S, M, P, r, 2) * 100;
      int own_bonus = is_own_side_region(M, P, r) ? 120 : 0;
      return P.hops[M.my_hq][r] * 10 + nearest_building_hops * 3 +
             center_risk + enemy_penalty - own_bonus;
    };
    int sa = score(a);
    int sb = score(b);
    if (sa != sb)
      return sa < sb;
    return a < b;
  });
  return targets;
}

[[maybe_unused]] static void assign_expansion_moves(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int max_new_moves) {
  std::vector<int> targets = sorted_expansion_targets(S, M, P);
  std::set<int> assigned;
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::MOVING)
      assigned.insert(w.target);
  }
  for (const auto &move_plan : a.moves) {
    int target = move_plan.second;
    assigned.insert(target);
  }

  int issued = 0;
  for (const auto &w : S.warriors) {
    if (issued >= max_new_moves)
      break;
    if (!can_move_non_emergency(S, M, a, w))
      continue;

    int best_target = -1;
    for (int target : targets) {
      if (assigned.count(target))
        continue;
      if (has_worker_heading_to(S, M, target))
        continue;
      if (P.nxt[w.region][target] == -1)
        continue;
      if (is_contested_region(S, M, P, target) && count_my_bases(S, M) < 2)
        continue;
      best_target = target;
      break;
    }
    if (best_target == -1)
      break;

    int routed_target = large_waypoint_or_target(S, M, P, w.region, best_target);
    int cost = move_cost_to(S, M, routed_target);
    if (planned_gold - cost < BASE_LEVELS[1].cost)
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, w, best_target))
      continue;
    assigned.insert(best_target);
    ++issued;
  }
}

static int affordable_train_count(int planned_gold, int cap) {
  return std::max(0, std::min(cap, planned_gold / TRAIN_COST));
}

[[maybe_unused]] static int pending_base_reservation(const GameState &S,
                                                     const GameMap &M) {
  std::set<int> targets;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::MOVING)
      continue;
    if (!is_stronghold(M, w.target))
      continue;
    if (find_building(S, w.target) != nullptr)
      continue;
    if (count_enemy_warriors_at(S, w.target, M) > 0)
      continue;
    targets.insert(w.target);
  }
  int remaining_slots = std::max(0, TARGET_BASE_COUNT - count_my_bases(S, M));
  return BASE_LEVELS[1].cost *
         std::min<int>(remaining_slots, static_cast<int>(targets.size()));
}

[[maybe_unused]] static bool has_ready_base_site(const GameState &S,
                                                 const GameMap &M) {
  if (count_my_bases(S, M) >= TARGET_BASE_COUNT)
    return false;
  for (int r : M.strongholds) {
    if (find_building(S, r) != nullptr)
      continue;
    if (count_my_warriors_at(S, r, M) > 0 &&
        count_enemy_warriors_at(S, r, M) == 0) {
      return true;
    }
  }
  return false;
}

static std::vector<const Warrior *> hq_ready_warriors(const GameState &S,
                                                      const GameMap &M) {
  std::vector<const Warrior *> ready;
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::STATIONARY &&
        w.region == M.my_hq) {
      ready.push_back(&w);
    }
  }
  std::sort(ready.begin(), ready.end(), [](const Warrior *a, const Warrior *b) {
    return a->id.num < b->id.num;
  });
  return ready;
}

static bool hq_threat_active(const GameState &S, const GameMap &M,
                             const Paths &P);

static const Building *hq_building_of(const GameState &S, const GameMap &M,
                                      Side side) {
  const Building *b = find_building(S, hq_of(M, side));
  return (b != nullptr && b->side == side && b->type == BType::HQ) ? b
                                                                   : nullptr;
}

static int warrior_hp_force_at(const GameState &S, int region, Side side,
                               bool stationary_only) {
  int force = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != side || w.region != region)
      continue;
    if (stationary_only && w.state != WState::STATIONARY)
      continue;
    force += std::max(1, w.hp);
  }
  return force;
}

static int observed_hq_level(const GameState &S, const GameMap &M, Side side) {
  const Building *hq = hq_building_of(S, M, side);
  return hq == nullptr ? 1 : std::max(1, std::min(HQ_MAX_LEVEL, hq->level));
}

static double enemy_hq_defense_estimate(const GameState &S, const GameMap &M,
                                        const Paths &P) {
  Side enemy = opposite(M.my_side);
  int enemy_hq_level = observed_hq_level(S, M, enemy);
  int travel_hops = P.hops[M.my_hq][M.opp_hq];
  if (travel_hops > M.N)
    travel_hops = M.N;
  double predicted_growth =
      static_cast<double>(travel_hops) * HQ_LEVELS[enemy_hq_level].train_cap *
      HQ_LEVELS[enemy_hq_level].warrior_hp * 0.7;
  double turret_buffer = static_cast<double>(enemy_hq_level * 4);
  return warrior_hp_force_at(S, M.opp_hq, enemy, false) + predicted_growth +
         turret_buffer;
}

[[maybe_unused]] static bool decisive_attack_ready(const GameState &S,
                                                   const GameMap &M,
                                                   const Paths &P,
                                                   int planned_gold) {
  if (hq_threat_active(S, M, P))
    return false;
  int my_hq_count = static_cast<int>(hq_ready_warriors(S, M).size());
  if (my_hq_count < 8)
    return false;
  int enemy_hq_count = count_enemy_warriors_at(S, M.opp_hq, M);
  if (enemy_hq_count > my_hq_count)
    return false;

  int my_force = warrior_hp_force_at(S, M.my_hq, M.my_side, true);
  double enemy_estimate = enemy_hq_defense_estimate(S, M, P);
  if (static_cast<double>(my_force) < enemy_estimate * 1.25)
    return false;

  int move_cost = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    move_cost += move_cost_to(S, M, M.opp_hq);
  }
  return move_cost > 0 && planned_gold >= move_cost;
}

static bool is_forward_base(const Building &b, const GameMap &M,
                            const Paths &P) {
  return b.type == BType::BASE &&
         P.dist[b.region][M.opp_hq] < P.dist[M.my_hq][M.opp_hq];
}

[[maybe_unused]] static bool try_base_upgrade(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, int reserve_gold) {
  const Building *best = nullptr;
  int best_score = std::numeric_limits<int>::min();
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE || b.level >= BASE_MAX_LEVEL)
      continue;
    if (!is_region_safe_for_build(S, M, b.region))
      continue;
    int cost = upgrade_cost(b);
    if (planned_gold - cost < reserve_gold)
      continue;
    int workers = count_my_warriors_at(S, b.region, M);
    int score = 0;
    if (b.level == 1 && workers >= 2)
      score += 300;
    if (b.level == 2 && workers >= 2)
      score += 150;
    if (is_forward_base(b, M, P))
      score += 120;
    score += workers * 30;
    score -= cost / 20;
    if (score > best_score) {
      best_score = score;
      best = &b;
    }
  }
  if (best == nullptr)
    return false;
  return add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                              best->region);
}

static bool hq_threat_active(const GameState &S, const GameMap &M,
                             const Paths &P) {
  if (count_enemy_warriors_at(S, M.my_hq, M) > 0)
    return true;
  return enemy_near_region(S, M, P, M.my_hq, 1) >= 2;
}

static bool hq_assault_urgent_threat_active(const GameState &S,
                                            const GameMap &M,
                                            const Paths &P) {
  if (count_enemy_warriors_at(S, M.my_hq, M) > 0)
    return true;
  int close = enemy_near_region(S, M, P, M.my_hq, 1);
  if (close < 4)
    return false;
  int defenders = count_my_stationary_at(S, M.my_hq, M);
  return defenders + 2 < close;
}

static bool sub90_early_hq_rush_signal(const GameState &S, const GameMap &M,
                                       const Paths &P, int turn) {
  if (large_strategy_active(M) || turn > 8)
    return false;
  int direct_hq_movers = 0;
  int nearby_pressure = 0;
  Side enemy = opposite(M.my_side);
  int enemy_hq = hq_of(M, enemy);
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side)
      continue;
    if (w.state == WState::MOVING && w.target == M.my_hq)
      ++direct_hq_movers;
    if (w.region != enemy_hq && P.hops[w.region][M.my_hq] <= 7)
      ++nearby_pressure;
  }
  if (direct_hq_movers >= 3)
    return true;
  return nearby_pressure >= 3;
}

static bool add_train_if_needed(const GameState &S, const GameMap &M,
                                Actions &a, int &planned_gold,
                                int wanted_train) {
  if (a.train_n > 0 || wanted_train <= 0)
    return false;
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr)
    return false;
  int train_n = std::min(wanted_train, affordable_train_count(
                                           planned_gold,
                                           HQ_LEVELS[hq->level].train_cap));
  if (train_n <= 0)
    return false;
  a.train_n = train_n;
  planned_gold -= a.train_n * TRAIN_COST;
  return true;
}

static bool add_train_if_needed_with_reserve(const GameState &S,
                                             const GameMap &M, Actions &a,
                                             int &planned_gold,
                                             int wanted_train,
                                             int reserve_gold) {
  if (reserve_gold <= 0)
    return add_train_if_needed(S, M, a, planned_gold, wanted_train);
  int train_gold = std::max(0, planned_gold - reserve_gold);
  int before = train_gold;
  if (!add_train_if_needed(S, M, a, train_gold, wanted_train))
    return false;
  planned_gold -= before - train_gold;
  return true;
}

struct ThreatInfo {
  bool active = false;
  int target_region = -1;
  bool hq_threat = false;
  int enemy_near = 0;
  int enemy_close = 0;
};

[[maybe_unused]] static ThreatInfo detect_threat(const GameState &S,
                                                 const GameMap &M,
                                                 const Paths &P) {
  ThreatInfo best;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    int near = enemy_near_region(S, M, P, b.region, 3);
    int close = enemy_near_region(S, M, P, b.region, 1);
    bool is_hq = b.type == BType::HQ;
    bool forward_base =
        b.type == BType::BASE && P.dist[b.region][M.opp_hq] < P.dist[M.my_hq][M.opp_hq];
    bool low_hp = b.hp <= std::max(3, b.current_hp() / 3);
    bool active = false;
    if (is_hq && (close >= 2 || near >= 3 || low_hp))
      active = true;
    if (forward_base && (close >= 3 || (near >= 4 && low_hp)))
      active = true;
    if (!active)
      continue;
    int severity = close * 10 + near + (is_hq ? 100 : 0) + (low_hp ? 20 : 0);
    int best_severity =
        best.enemy_close * 10 + best.enemy_near + (best.hq_threat ? 100 : 0);
    if (!best.active || severity > best_severity) {
      best.active = true;
      best.target_region = b.region;
      best.hq_threat = is_hq;
      best.enemy_near = near;
      best.enemy_close = close;
    }
  }
  return best;
}

[[maybe_unused]] static const Building *best_rally_building(
    const GameState &S, const GameMap &M, const Paths &P) {
  const Building *best = nullptr;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    if (b.type == BType::BASE && count_enemy_warriors_at(S, b.region, M) == 0 &&
        enemy_near_region(S, M, P, b.region, 2) <=
            count_my_warriors_at(S, b.region, M) + 1) {
      if (best == nullptr || P.dist[b.region][M.opp_hq] < P.dist[best->region][M.opp_hq])
        best = &b;
    }
  }
  if (best != nullptr)
    return best;
  return my_hq_building(S, M);
}

[[maybe_unused]] static const Building *
forward_rally_base(const GameState &S, const GameMap &M, const Paths &P) {
  const Building *best = nullptr;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    if (P.nxt[b.region][M.opp_hq] == -1)
      continue;
    if (best == nullptr || P.dist[b.region][M.opp_hq] <
                               P.dist[best->region][M.opp_hq]) {
      best = &b;
    }
  }
  return best;
}

static int effective_my_count_at(const GameState &S, const Actions &a,
                                 int region, const GameMap &M) {
  return count_my_stationary_at(S, region, M) -
         planned_moves_from_region(a, S, region) +
         planned_moves_to_region(a, region);
}

static int build_phase_stationary_count_at(const GameState &S,
                                           const Actions &a, int region,
                                           const GameMap &M) {
  return count_my_stationary_at(S, region, M) -
         planned_moves_from_region(a, S, region);
}

static int committed_my_count_at(const GameState &S, const Actions &a,
                                 int region, const GameMap &M) {
  int count = count_my_stationary_at(S, region, M);
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::MOVING &&
        w.target == region) {
      ++count;
    }
  }
  return count - planned_moves_from_region(a, S, region) +
         planned_moves_to_region(a, region);
}

static bool add_surplus_moves_to_region(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int target,
                                        int max_moves,
                                        int protected_region = -1,
                                        int protected_need = 0) {
  if (max_moves <= 0 || target < 0 || target >= M.N)
    return false;
  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (w.region == target)
      continue;
    if (!can_move_non_emergency(S, M, a, w))
      continue;
    if (is_stronghold(M, w.region) && find_building(S, w.region) == nullptr)
      continue;
    if (P.nxt[w.region][target] == -1)
      continue;
    if (would_pull_forward_pressure_back(M, P, w.region, target))
      continue;
    if (w.region == protected_region) {
      int after_departures =
          count_my_stationary_at(S, w.region, M) -
          planned_moves_from_region(a, S, w.region);
      if (after_departures <= protected_need)
        continue;
    }
    candidates.push_back(&w);
  }
  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.dist[lhs->region][target] != P.dist[rhs->region][target])
                return P.dist[lhs->region][target] <
                       P.dist[rhs->region][target];
              return lhs->id.num < rhs->id.num;
            });

  int issued = 0;
  for (const Warrior *w : candidates) {
    if (issued >= max_moves)
      break;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, target))
      continue;
    ++issued;
  }
  return issued > 0;
}

static int minimum_base_staff(const Building &b) {
  if (b.type != BType::BASE)
    return 0;
  return 1;
}

static int large_base_level_staff_deficit(const GameState &S, const Actions &a,
                                          const GameMap &M) {
  if (!large_strategy_active(M))
    return 0;
  int deficit = 0;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    int have = committed_my_count_at(S, a, b.region, M);
    deficit += std::max(0, large_base_staff_need(b) - have);
  }
  return deficit;
}

static bool add_excess_base_moves_to_hq(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int max_moves,
                                        int protected_region = -1,
                                        int protected_need = 0) {
  bool issued_any = false;
  int issued = 0;
  while (issued < max_moves) {
    const Warrior *best = nullptr;
    int best_surplus = 0;
    for (const auto &w : S.warriors) {
      if (w.id.side != M.my_side || w.state != WState::STATIONARY)
        continue;
      if (w.region == M.my_hq || warrior_already_planned(a, w.id))
        continue;
      const Building *b = find_building(S, w.region);
      if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
        continue;
      if (count_enemy_warriors_at(S, w.region, M) > 0)
        continue;
      if (P.nxt[w.region][M.my_hq] == -1)
        continue;
      if (would_pull_forward_pressure_back(M, P, w.region, M.my_hq))
        continue;
      int after_departures =
          count_my_stationary_at(S, w.region, M) -
          planned_moves_from_region(a, S, w.region);
      int required = large_strategy_active(M) ? large_base_staff_need(*b) : minimum_base_staff(*b);
      if (w.region == protected_region)
        required = std::max(required, protected_need);
      int surplus = after_departures - required;
      if (surplus <= 0)
        continue;
      if (best == nullptr || surplus > best_surplus ||
          (surplus == best_surplus && w.id.num > best->id.num)) {
        best = &w;
        best_surplus = surplus;
      }
    }
    if (best == nullptr)
      break;
    int cost = move_cost_to(S, M, M.my_hq);
    if (planned_gold < cost)
      break;
    if (!can_leave_large_base_strict(S, M, a, best->region))
      break;
    a.moves.emplace_back(best->id, M.my_hq);
    planned_gold -= cost;
    issued_any = true;
    ++issued;
  }
  return issued_any;
}

static int total_worker_deficit(const GameState &S, const Actions &a,
                                const GameMap &M) {
  int deficit = 0;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    int have = committed_my_count_at(S, a, b.region, M);
    deficit += std::max(0, b.work_cap() - have);
  }
  return deficit;
}

static int minimum_staff_deficit(const GameState &S, const Actions &a,
                                 const GameMap &M) {
  int deficit = 0;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    int have = committed_my_count_at(S, a, b.region, M);
    deficit += std::max(0, 1 - have);
  }
  return deficit;
}

static bool add_critical_worker_fill_moves(const GameState &S, const GameMap &M,
                                           const Paths &P, Actions &a,
                                           int &planned_gold) {
  struct Need {
    int region;
    double score;
  };
  std::vector<Need> needs;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    if (committed_my_count_at(S, a, b.region, M) >= 1)
      continue;
    double score = P.dist[M.my_hq][b.region];
    if (b.type == BType::HQ)
      score -= 2000.0;
    needs.push_back(Need{b.region, score});
  }
  std::sort(needs.begin(), needs.end(),
            [](const Need &lhs, const Need &rhs) {
              if (lhs.score != rhs.score)
                return lhs.score < rhs.score;
              return lhs.region < rhs.region;
            });

  bool issued = false;
  for (const Need &need : needs) {
    if (add_surplus_moves_to_region(S, M, P, a, planned_gold, need.region, 1))
      issued = true;
  }
  return issued;
}

static bool add_worker_fill_moves(const GameState &S, const GameMap &M,
                                  const Paths &P, Actions &a,
                                  int &planned_gold) {
  struct Need {
    int region;
    int need;
    double score;
  };
  std::vector<Need> needs;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    int have = committed_my_count_at(S, a, b.region, M);
    int need = b.work_cap() - have;
    if (need <= 0)
      continue;
    double score = (b.level >= 2 ? -1000.0 : 0.0) + P.dist[M.my_hq][b.region];
    needs.push_back(Need{b.region, need, score});
  }
  std::sort(needs.begin(), needs.end(),
            [](const Need &lhs, const Need &rhs) {
              if (lhs.score != rhs.score)
                return lhs.score < rhs.score;
              return lhs.region < rhs.region;
            });

  bool issued = false;
  for (const Need &need : needs) {
    int still_needed = need.need;
    while (still_needed > 0 &&
           add_surplus_moves_to_region(S, M, P, a, planned_gold, need.region,
                                       1)) {
      issued = true;
      --still_needed;
    }
  }
  return issued;
}

static bool add_sub90_post_defense_base_refill(const GameState &S,
                                               const GameMap &M,
                                               const Paths &P, Actions &a,
                                               int &planned_gold,
                                               const Building *hq) {
  if (large_strategy_active(M) || hq == nullptr)
    return false;
  if (count_enemy_warriors_at(S, M.my_hq, M) > 0)
    return false;
  if (enemy_near_region(S, M, P, M.my_hq, 1) > 0)
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;

  int hq_ready = count_my_stationary_at(S, M.my_hq, M) -
                 planned_moves_from_region(a, S, M.my_hq);
  int reserve = enemy_near_region(S, M, P, M.my_hq, 2) > 0 ? 3 : 2;
  if (hq_ready <= reserve)
    return false;

  struct Need {
    int region;
    double score;
  };
  std::vector<Need> needs;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    if (committed_my_count_at(S, a, b.region, M) >= 1)
      continue;
    if (P.nxt[M.my_hq][b.region] == -1)
      continue;
    needs.push_back(Need{b.region, P.dist[M.my_hq][b.region]});
  }
  if (needs.empty())
    return false;
  std::sort(needs.begin(), needs.end(),
            [](const Need &lhs, const Need &rhs) {
              if (lhs.score != rhs.score)
                return lhs.score < rhs.score;
              return lhs.region < rhs.region;
            });

  const Warrior *best = nullptr;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region != M.my_hq || warrior_already_planned(a, w.id))
      continue;
    if (best == nullptr || w.id.num < best->id.num)
      best = &w;
  }
  if (best == nullptr)
    return false;

  int target = needs.front().region;
  int cost = move_cost_to(S, M, target);
  if (planned_gold < cost)
    return false;
  a.moves.emplace_back(best->id, target);
  planned_gold -= cost;
  return true;
}

static bool add_common_base_surplus_attack_join_moves(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int attack_target);

static bool add_rally_attack_if_ready(const GameState &S, const GameMap &M,
                                      const Paths &P, Actions &a,
                                      int &planned_gold,
                                      const Building *rally) {
  if (rally == nullptr)
    return false;
  std::vector<const Warrior *> attackers;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region != rally->region || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    attackers.push_back(&w);
  }
  if (static_cast<int>(attackers.size()) < RALLY_ATTACK_COUNT)
    return false;
  int reserve = reserve_need_at_region(S, M, rally->region);
  int available_attackers =
      std::max(0, static_cast<int>(attackers.size()) - reserve);
  int launch_count =
      std::min<int>(available_attackers, std::max(0, planned_gold / MOVE_COST));
  if (launch_count < RALLY_ATTACK_COUNT)
    return false;
  std::sort(attackers.begin(), attackers.end(),
            [](const Warrior *lhs, const Warrior *rhs) {
              return lhs->id.num < rhs->id.num;
            });
  int issued = 0;
  for (const Warrior *w : attackers) {
    if (issued >= launch_count)
      break;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, M.opp_hq))
      continue;
    ++issued;
  }
  if (issued > 0)
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  return issued >= RALLY_ATTACK_COUNT;
}

static bool add_rally_gather_moves(const GameState &S, const GameMap &M,
                                   const Paths &P, Actions &a,
                                   int &planned_gold,
                                   const Building *rally) {
  if (rally == nullptr)
    return false;
  int have = committed_my_count_at(S, a, rally->region, M);
  int need = RALLY_ATTACK_COUNT - have;
  if (need <= 0)
    return false;
  return add_surplus_moves_to_region(S, M, P, a, planned_gold, rally->region,
                                     need);
}

[[maybe_unused]] static std::vector<const Warrior *> selectable_attackers(
    const GameState &S, const GameMap &M, const Paths &P, const Actions &a,
    bool allow_reserved) {
  std::vector<const Warrior *> out;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    if (w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq)
      continue;
    if (warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!allow_reserved && !can_move_non_emergency(S, M, a, w))
      continue;
    out.push_back(&w);
  }
  std::sort(out.begin(), out.end(), [&](const Warrior *a, const Warrior *b) {
    bool a_surplus = can_move_non_emergency(S, M, Actions{}, *a);
    bool b_surplus = can_move_non_emergency(S, M, Actions{}, *b);
    if (a_surplus != b_surplus)
      return a_surplus > b_surplus;
    if (P.dist[a->region][M.opp_hq] != P.dist[b->region][M.opp_hq])
      return P.dist[a->region][M.opp_hq] < P.dist[b->region][M.opp_hq];
    if (a->id.num != b->id.num)
      return a->id.num < b->id.num;
    return a->region < b->region;
  });
  return out;
}

static std::vector<int> log2_target_order(const GameState &S, const GameMap &M,
                                          const Paths &P) {
  const std::vector<int> left_targets = {2, 4, 27, 21, 3, 43, 42, 53, 41, 65};
  std::vector<int> out;
  std::set<int> used;

  auto add_target = [&](int wanted) {
    const Building *wanted_building =
        (wanted >= 0 && wanted < M.N) ? find_building(S, wanted) : nullptr;
    if (wanted >= 0 && wanted < M.N && is_stronghold(M, wanted) &&
        !used.count(wanted) &&
        (wanted_building == nullptr || wanted_building->side == M.my_side)) {
      out.push_back(wanted);
      used.insert(wanted);
      return;
    }

    int best = -1;
    double best_score = std::numeric_limits<double>::infinity();
    for (int r : M.strongholds) {
      if (used.count(r))
        continue;
      if (find_building(S, r) != nullptr &&
          find_building(S, r)->side != M.my_side)
        continue;
      bool same_side = P.dist[M.my_hq][r] <= P.dist[M.opp_hq][r];
      double side_penalty = same_side ? 0.0 : 100000.0;
      double score = side_penalty + std::abs(r - wanted) * 100.0 +
                     P.dist[M.my_hq][r];
      if (score < best_score) {
        best_score = score;
        best = r;
      }
    }
    if (best != -1) {
      out.push_back(best);
      used.insert(best);
    }
  };

  for (int r : left_targets) {
    int target = (M.my_side == Side::LEFT) ? r : (M.N - 1 - r);
    add_target(target);
  }

  struct ExtraTarget {
    int region;
    double score;
  };
  std::vector<ExtraTarget> extras;
  for (int r : M.strongholds) {
    if (used.count(r))
      continue;
    const Building *b = find_building(S, r);
    if (b != nullptr && b->side != M.my_side)
      continue;
    bool same_side = P.dist[M.my_hq][r] <= P.dist[M.opp_hq][r];
    double side_penalty = same_side ? 0.0 : 100000.0;
    extras.push_back(ExtraTarget{r, side_penalty + P.dist[M.my_hq][r]});
  }
  std::sort(extras.begin(), extras.end(),
            [](const ExtraTarget &lhs, const ExtraTarget &rhs) {
              if (lhs.score != rhs.score)
                return lhs.score < rhs.score;
              return lhs.region < rhs.region;
            });
  for (const ExtraTarget &extra : extras) {
    if (static_cast<int>(out.size()) >= TARGET_BASE_COUNT)
      break;
    out.push_back(extra.region);
    used.insert(extra.region);
  }
  return out;
}

static int active_macro_target_goal(const GameState &S, const GameMap &M,
                                    const Paths &P) {
  return std::min(TARGET_BASE_COUNT,
                  static_cast<int>(log2_target_order(S, M, P).size()));
}

static bool is_my_base_at(const GameState &S, const GameMap &M, int region) {
  const Building *b = find_building(S, region);
  return b != nullptr && b->side == M.my_side && b->type == BType::BASE;
}

static int count_target_bases_built(const GameState &S, const GameMap &M,
                                    const Paths &P) {
  int count = 0;
  for (int r : log2_target_order(S, M, P)) {
    if (is_my_base_at(S, M, r))
      ++count;
  }
  return count;
}

static bool enemy_building_at(const GameState &S, const GameMap &M,
                              int region) {
  const Building *b = find_building(S, region);
  return b != nullptr && b->side != M.my_side;
}

static int next_unbuilt_target(const GameState &S, const GameMap &M,
                               const Paths &P) {
  for (int r : log2_target_order(S, M, P)) {
    if (enemy_building_at(S, M, r))
      continue;
    if (!is_my_base_at(S, M, r))
      return r;
  }
  return -1;
}

static bool has_target_worker_or_pending(const GameState &S,
                                         const GameMap &M, int target) {
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    if (w.region == target && w.state == WState::STATIONARY)
      return true;
    if (w.state == WState::MOVING && w.target == target)
      return true;
  }
  return false;
}

static bool has_worker_or_pending_for_target(const GameState &S,
                                             const GameMap &M, int target) {
  return has_target_worker_or_pending(S, M, target);
}

static const Building *next_level1_target_base(const GameState &S,
                                               const GameMap &M,
                                               const Paths &P) {
  for (int r : log2_target_order(S, M, P)) {
    const Building *b = find_building(S, r);
    if (b != nullptr && b->side == M.my_side && b->type == BType::BASE &&
        b->level == 1) {
      return b;
    }
  }
  return nullptr;
}

static int next_level1_upgrade_target_region(const GameState &S,
                                             const GameMap &M,
                                             const Paths &P) {
  int income = std::max(0, estimate_income(S, M));
  bool all_targets_built =
      count_target_bases_built(S, M, P) >= TARGET_BASE_COUNT;
  for (int r : log2_target_order(S, M, P)) {
    const Building *b = find_building(S, r);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
      continue;
    if (b->level != 1)
      continue;
    if (count_enemy_warriors_at(S, r, M) > 0)
      continue;
    if (committed_my_count_at(S, Actions{}, r, M) >= 2)
      return r;
    if (all_targets_built)
      return r;
    int travel_turns = P.hops[M.my_hq][r];
    if (travel_turns > M.N)
      continue;
    if (S.gold + income * std::max(1, travel_turns) >= upgrade_cost(*b))
      return r;
  }
  return -1;
}

static int count_target_level2_bases(const GameState &S, const GameMap &M,
                                     const Paths &P) {
  int count = 0;
  for (int r : log2_target_order(S, M, P)) {
    const Building *b = find_building(S, r);
    if (b != nullptr && b->side == M.my_side && b->type == BType::BASE &&
        b->level >= 2) {
      ++count;
    }
  }
  return count;
}

static int target_base_worker_deficit(const GameState &S, const Actions &a,
                                      const GameMap &M, const Paths &P) {
  int deficit = 0;
  for (int r : log2_target_order(S, M, P)) {
    const Building *b = find_building(S, r);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
      continue;
    int need = std::max(1, std::min(BASE_MAX_LEVEL, b->level));
    int have = effective_my_count_at(S, a, r, M);
    deficit += std::max(0, need - have);
  }
  return deficit;
}

static bool has_open_neutral_target(const GameState &S, const GameMap &M,
                                    const Paths &P) {
  for (int r : log2_target_order(S, M, P)) {
    if (find_building(S, r) != nullptr)
      continue;
    if (count_enemy_warriors_at(S, r, M) > 0)
      continue;
    if (P.nxt[M.my_hq][r] == -1)
      continue;
    return true;
  }
  return false;
}

static int core_level2_goal(int active_target_goal) {
  if (active_target_goal <= 0)
    return 0;
  return std::min(active_target_goal, 4);
}

static int count_forward_my_bases(const GameState &S, const GameMap &M,
                                  const Paths &P) {
  int count = 0;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    if (P.dist[b.region][M.opp_hq] < P.dist[M.my_hq][b.region])
      ++count;
  }
  return count;
}

static int nearest_my_building_hops(const GameState &S, const GameMap &M,
                                    const Paths &P, int region) {
  int best = M.N + 1;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    best = std::min(best, P.hops[b.region][region]);
  }
  return best;
}

static double center_first_enemy_base_score(const GameState &S,
                                            const GameMap &M,
                                            const Paths &P,
                                            const Building &b) {
  int center = M.N / 2;
  int center_hops = P.hops[center][b.region];
  int opp_hq_hops = P.hops[b.region][M.opp_hq];
  int my_hq_hops = P.hops[M.my_hq][b.region];
  int nearest_hops = nearest_my_building_hops(S, M, P, b.region);
  if (center_hops < 0 || opp_hq_hops < 0 || my_hq_hops < 0 ||
      nearest_hops > M.N) {
    return std::numeric_limits<double>::infinity();
  }

  int enemy_here = count_enemy_warriors_at(S, b.region, M);
  int enemy_near = enemy_near_region(S, M, P, b.region, 1);
  double opp_hq_near_penalty =
      std::max(0, 7 - opp_hq_hops) * 320.0 +
      (opp_hq_hops <= 2 ? 1400.0 : 0.0);

  return center_hops * 1200.0 + opp_hq_near_penalty -
         opp_hq_hops * 18.0 + nearest_hops * 12.0 + my_hq_hops * 2.0 +
         b.level * 45.0 + b.hp * 5.0 + enemy_here * 90.0 +
         enemy_near * 35.0;
}

static int select_forward_capture_target(const GameState &S,
                                         const GameMap &M, const Paths &P,
                                         int current_target) {
  (void)current_target;

  int best = -1;
  double best_score = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side || b.type != BType::BASE)
      continue;
    if (P.nxt[M.my_hq][b.region] == -1)
      continue;
    double score = center_first_enemy_base_score(S, M, P, b);
    if (score < best_score) {
      best_score = score;
      best = b.region;
    }
  }
  return best;
}

static bool common_attack_target_usable(const GameState &S, const GameMap &M,
                                        const Paths &P, int target) {
  if (target == M.opp_hq)
    return P.nxt[M.my_hq][M.opp_hq] != -1;
  if (target < 0 || target >= M.N)
    return false;
  const Building *b = find_building(S, target);
  return b != nullptr && b->side != M.my_side && b->type == BType::BASE &&
         P.nxt[M.my_hq][target] != -1;
}

static int resolve_common_base_surplus_attack_target(
    const GameState &S, const GameMap &M, const Paths &P, int attack_target) {
  if (common_attack_target_usable(S, M, P, attack_target))
    return attack_target;
  int fallback = select_forward_capture_target(S, M, P, attack_target);
  if (common_attack_target_usable(S, M, P, fallback))
    return fallback;
  return M.opp_hq;
}

static int early_large_attack_committed_count(const GameState &S,
                                             const GameMap &M,
                                             const Actions &a, int target);
static bool large_early_attack_gate_satisfied(const GameState &S,
                                             const GameMap &M,
                                             const Actions &a, int target,
                                             int candidate_count,
                                             int planned_gold);

static bool add_common_base_surplus_attack_join_moves(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int attack_target) {
  attack_target =
      resolve_common_base_surplus_attack_target(S, M, P, attack_target);
  if (!common_attack_target_usable(S, M, P, attack_target))
    return false;

  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == attack_target || warrior_already_planned(a, w.id))
      continue;
    const Building *src = find_building(S, w.region);
    if (src == nullptr || src->side != M.my_side || src->type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, src->region, M) > 0)
      continue;
    int after_departures = count_my_stationary_at(S, src->region, M) -
                           planned_moves_from_region(a, S, src->region);
    if (after_departures <= base_attack_staff_need(*src))
      continue;
    if (P.nxt[w.region][attack_target] == -1)
      continue;
    if (attack_target != M.opp_hq &&
        would_pull_forward_pressure_back(M, P, w.region, attack_target))
      continue;
    candidates.push_back(&w);
  }
  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][attack_target] !=
                  P.hops[rhs->region][attack_target]) {
                return P.hops[lhs->region][attack_target] <
                       P.hops[rhs->region][attack_target];
              }
              if (lhs->region != rhs->region)
                return lhs->region < rhs->region;
              return lhs->id.num < rhs->id.num;
            });

  bool issued = false;
  bool enforce_large_target_group =
      large_strategy_active(M) && large_final_goal_useful(S, M, attack_target);
  if (enforce_large_target_group &&
      !large_early_attack_gate_satisfied(
          S, M, a, attack_target, static_cast<int>(candidates.size()),
          planned_gold))
    return false;
  int gate_committed = enforce_large_target_group
                           ? early_large_attack_committed_count(S, M, a,
                                                                attack_target)
                           : 0;
  size_t move_mark = a.moves.size();
  int gold_mark = planned_gold;
  std::vector<std::pair<WarriorId, int>> saved_goal_mark;
  int issued_count = 0;
  for (const Warrior *w : candidates) {
    const Building *src = find_building(S, w->region);
    if (src == nullptr || src->side != M.my_side || src->type != BType::BASE)
      continue;
    int after_departures = count_my_stationary_at(S, src->region, M) -
                           planned_moves_from_region(a, S, src->region);
    if (after_departures <= base_attack_staff_need(*src))
      continue;
    int old_goal = large_goal_saved(w->id);
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w,
                                      attack_target))
      continue;
    if (enforce_large_target_group)
      saved_goal_mark.emplace_back(w->id, old_goal);
    issued = true;
    ++issued_count;
  }
  if (enforce_large_target_group && gate_committed + issued_count < 3) {
    a.moves.resize(move_mark);
    planned_gold = gold_mark;
    for (const auto &entry : saved_goal_mark) {
      if (entry.second >= 0)
        large_goal_remember(entry.first, entry.second);
      else
        large_goal_clear(entry.first);
    }
    return false;
  }
  return issued;
}

static void idle_base_surplus_ensure(int num) {
  if (num <= 0)
    return;
  if (static_cast<int>(g_idle_base_surplus_turns_by_warrior.size()) <= num)
    g_idle_base_surplus_turns_by_warrior.resize(num + 1, 0);
}

static int idle_base_surplus_turns(WarriorId id) {
  if (id.num <= 0 ||
      static_cast<int>(g_idle_base_surplus_turns_by_warrior.size()) <= id.num)
    return 0;
  return g_idle_base_surplus_turns_by_warrior[id.num];
}

static void update_idle_base_surplus_turns(const GameState &S,
                                           const GameMap &M) {
  std::set<int> surplus_nums;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    std::vector<const Warrior *> stationed;
    for (const auto &w : S.warriors) {
      if (w.id.side == M.my_side && w.state == WState::STATIONARY &&
          w.region == b.region) {
        stationed.push_back(&w);
      }
    }
    std::sort(stationed.begin(), stationed.end(),
              [](const Warrior *lhs, const Warrior *rhs) {
                return lhs->id.num < rhs->id.num;
              });
    int keep = building_attack_staff_need(b);
    for (int i = keep; i < static_cast<int>(stationed.size()); ++i)
      surplus_nums.insert(stationed[i]->id.num);
  }

  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.id.num <= 0)
      continue;
    idle_base_surplus_ensure(w.id.num);
    if (surplus_nums.count(w.id.num))
      ++g_idle_base_surplus_turns_by_warrior[w.id.num];
    else
      g_idle_base_surplus_turns_by_warrior[w.id.num] = 0;
  }
}

static int remaining_gold_after_actions(const GameState &S, const GameMap &M,
                                        const Actions &a) {
  int gold = std::max(0, S.gold);
  for (int region : a.upgrades) {
    int cost = planned_upgrade_cost(S, M, region);
    if (cost < std::numeric_limits<int>::max() / 8)
      gold -= cost;
  }
  for (const auto &move_plan : a.moves)
    gold -= move_cost_to(S, M, move_plan.second);
  gold -= a.train_n * TRAIN_COST;
  return std::max(0, gold);
}

static int active_common_attack_target_from_plan(const GameState &S,
                                                 const GameMap &M,
                                                 const Paths &P,
                                                 const Actions &a) {
  int best = -1;
  int best_count = -1;
  int best_hops = 1000000;
  for (const auto &move_plan : a.moves) {
    int target = move_plan.second;
    if (!common_attack_target_usable(S, M, P, target))
      continue;
    int count = planned_moves_to_region(a, target);
    int hops = P.hops[M.my_hq][target];
    if (target == M.opp_hq)
      count += 1000;
    if (count > best_count || (count == best_count && hops < best_hops)) {
      best = target;
      best_count = count;
      best_hops = hops;
    }
  }
  return best;
}

static bool protect_idle_surplus_source(const GameState &S, const GameMap &M,
                                        const Actions &a, const Building &b,
                                        int turn, int surplus_after) {
  if (count_enemy_warriors_at(S, b.region, M) > 0)
    return true;
  if (b.type == BType::HQ)
    return turn < 90;
  if (b.region == g_hq_assault_rally_region && turn < 170)
    return true;
  if (planned_moves_to_region(a, b.region) > 0 && turn < 140 &&
      surplus_after <= 3)
    return true;
  return false;
}

static int early_large_attack_committed_count(const GameState &S,
                                             const GameMap &M,
                                             const Actions &a, int target) {
  int count = count_my_stationary_at(S, target, M) -
              planned_moves_from_region(a, S, target) +
              planned_moves_to_region(a, target);
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::MOVING)
      continue;
    if (w.target == target || large_goal_saved(w.id) == target)
      ++count;
  }
  return count;
}

static bool large_early_attack_gate_satisfied(const GameState &S,
                                             const GameMap &M,
                                             const Actions &a, int target,
                                             int candidate_count,
                                             int planned_gold) {
  if (!large_strategy_active(M))
    return true;
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr || hq->level < 2)
    return false;
  int missing = 3 - early_large_attack_committed_count(S, M, a, target);
  if (missing <= 0)
    return true;
  if (candidate_count < missing)
    return false;
  return planned_gold >= missing * MOVE_COST;
}

static bool add_idle_base_surplus_drain_moves(const GameState &S,
                                              const GameMap &M,
                                              const Paths &P, Actions &a,
                                              int &planned_gold, int turn) {
  int planned_attack_target =
      active_common_attack_target_from_plan(S, M, P, a);
  bool active_attack_plan = planned_attack_target >= 0;
  int attack_target = planned_attack_target;
  attack_target =
      resolve_common_base_surplus_attack_target(S, M, P, attack_target);
  if (!common_attack_target_usable(S, M, P, attack_target))
    return false;

  struct Candidate {
    const Warrior *w;
    int idle_turns;
  };
  std::vector<Candidate> candidates;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == attack_target || warrior_already_planned(a, w.id))
      continue;
    const Building *src = find_building(S, w.region);
    if (src == nullptr || src->side != M.my_side)
      continue;
    if (src->type == BType::HQ && !active_attack_plan && turn < 130)
      continue;
    int after_departures = count_my_stationary_at(S, src->region, M) -
                           planned_moves_from_region(a, S, src->region);
    int staff_need = building_attack_staff_need(*src);
    if (after_departures <= staff_need)
      continue;
    int surplus_after = after_departures - staff_need;
    if (protect_idle_surplus_source(S, M, a, *src, turn, surplus_after))
      continue;
    int idle_turns = idle_base_surplus_turns(w.id);
    int required_idle =
        active_attack_plan && (attack_target == M.opp_hq || turn >= 110) ? 0 : 2;
    if (idle_turns < required_idle)
      continue;
    if (P.nxt[w.region][attack_target] == -1)
      continue;
    if (attack_target != M.opp_hq &&
        would_pull_forward_pressure_back(M, P, w.region, attack_target))
      continue;
    candidates.push_back({&w, idle_turns});
  }

  std::sort(candidates.begin(), candidates.end(),
            [&](const Candidate &lhs, const Candidate &rhs) {
              if (lhs.idle_turns != rhs.idle_turns)
                return lhs.idle_turns > rhs.idle_turns;
              if (P.hops[lhs.w->region][attack_target] !=
                  P.hops[rhs.w->region][attack_target]) {
                return P.hops[lhs.w->region][attack_target] <
                       P.hops[rhs.w->region][attack_target];
              }
              if (lhs.w->region != rhs.w->region)
                return lhs.w->region < rhs.w->region;
              return lhs.w->id.num < rhs.w->id.num;
            });

  if (!active_attack_plan &&
      !large_early_attack_gate_satisfied(
          S, M, a, attack_target, static_cast<int>(candidates.size()),
          planned_gold))
    return false;

  bool issued = false;
  for (const Candidate &cand : candidates) {
    const Warrior &w = *cand.w;
    const Building *src = find_building(S, w.region);
    if (src == nullptr || src->side != M.my_side)
      continue;
    if (src->type == BType::HQ && !active_attack_plan && turn < 130)
      continue;
    int after_departures = count_my_stationary_at(S, src->region, M) -
                           planned_moves_from_region(a, S, src->region);
    int staff_need = building_attack_staff_need(*src);
    if (after_departures <= staff_need)
      continue;
    int surplus_after = after_departures - staff_need;
    if (protect_idle_surplus_source(S, M, a, *src, turn, surplus_after))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, w,
                                      attack_target))
      continue;
    issued = true;
  }
  return issued;
}

static void trim_final_turn_unusable_train(const GameState &S,
                                           const GameMap &M, const Actions &a,
                                           int turn, int &train_n) {
  if (turn < MAX_TURN || train_n <= 0)
    return;
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr)
    return;
  int staying = count_my_stationary_at(S, M.my_hq, M) -
                planned_moves_from_region(a, S, M.my_hq);
  int room = std::max(0, building_attack_staff_need(*hq) - staying);
  train_n = std::min(train_n, room);
}

static int capture_attack_need(const GameState &S, const GameMap &M,
                               const Paths &P, int target) {
  const Building *b = find_building(S, target);
  if (b == nullptr || b->side == M.my_side || b->type != BType::BASE)
    return 0;
  int need = 4;
  need += count_enemy_warriors_at(S, target, M);
  need += enemy_near_region(S, M, P, target, 1) / 2;
  need += std::max(0, b->hp + 5) / 6;
  need += std::max(0, b->level - 1);
  if (P.hops[M.my_hq][target] >= 8)
    ++need;
  return std::min(12, std::max(4, need));
}

static bool add_forward_base_builds(const GameState &S, const GameMap &M,
                                    Actions &a,
                                    std::set<int> &used_upgrades,
                                    int &planned_gold,
                                    int &planned_own_buildings,
                                    const std::set<int> &capture_regions) {
  bool issued = false;
  for (int region : capture_regions) {
    if (used_upgrades.count(region))
      continue;
    if (!is_stronghold(M, region))
      continue;
    if (find_building(S, region) != nullptr)
      continue;
    if (!is_region_safe_for_build(S, M, region))
      continue;
    if (committed_my_count_at(S, Actions{}, region, M) <= 0)
      continue;
    if (planned_gold < BASE_LEVELS[1].cost)
      continue;
    a.upgrades.push_back(region);
    used_upgrades.insert(region);
    planned_gold -= BASE_LEVELS[1].cost;
    ++planned_own_buildings;
    issued = true;
  }
  return issued;
}

static bool captured_base_build_waiting(
    const GameState &S, const GameMap &M, const std::set<int> &used_upgrades,
    const std::set<int> &capture_regions) {
  for (int region : capture_regions) {
    if (used_upgrades.count(region))
      continue;
    if (!is_stronghold(M, region))
      continue;
    if (find_building(S, region) != nullptr)
      continue;
    if (!is_region_safe_for_build(S, M, region))
      continue;
    if (committed_my_count_at(S, Actions{}, region, M) <= 0)
      continue;
    return true;
  }
  return false;
}

static bool add_forward_capture_moves(const GameState &S, const GameMap &M,
                                      const Paths &P, Actions &a,
                                      int &planned_gold, int target,
                                      int desired_attackers,
                                      const std::set<int> &capture_regions) {
  if (target < 0 || desired_attackers <= 0)
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;
  const Building *hq = my_hq_building(S, M);
  bool enforce_large_target_group =
      large_strategy_active(M) && large_final_goal_useful(S, M, target);
  if (enforce_large_target_group && (hq == nullptr || hq->level < 2))
    return false;

  int committed = count_my_warriors_at(S, target, M) +
                  planned_moves_to_region(a, target);
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::MOVING &&
        w.target == target) {
      ++committed;
    }
  }
  int need = std::max(0, desired_attackers - committed);
  if (need <= 0)
    return false;

  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (is_committed_hq_assault_warrior(w, M))
      continue;
    if (!can_move_non_emergency(S, M, a, w))
      continue;
    if (w.region == M.my_hq && hq != nullptr) {
      int extra_reserve = 0;
      int after_departures = count_my_stationary_at(S, M.my_hq, M) -
                             planned_moves_from_region(a, S, M.my_hq);
      if (after_departures <= hq->work_cap() + extra_reserve)
        continue;
    }
    if (capture_regions.count(w.region)) {
      const Building *src = find_building(S, w.region);
      if (src != nullptr && src->side == M.my_side && src->type == BType::BASE) {
        int required = 1;
        int after_departures = count_my_stationary_at(S, w.region, M) -
                               planned_moves_from_region(a, S, w.region);
        if (after_departures <= required)
          continue;
      }
    }
    if (is_stronghold(M, w.region) && find_building(S, w.region) == nullptr)
      continue;
    if (P.nxt[w.region][target] == -1)
      continue;
    candidates.push_back(&w);
  }
  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.dist[lhs->region][target] != P.dist[rhs->region][target])
                return P.dist[lhs->region][target] <
                       P.dist[rhs->region][target];
              return lhs->id.num < rhs->id.num;
            });

  int issued = 0;
  size_t move_mark = a.moves.size();
  int gold_mark = planned_gold;
  int gate_committed = enforce_large_target_group
                           ? early_large_attack_committed_count(S, M, a, target)
                           : 0;
  std::vector<std::pair<WarriorId, int>> saved_goal_mark;
  for (const Warrior *w : candidates) {
    if (issued >= need)
      break;
    int old_goal = large_goal_saved(w->id);
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, target))
      continue;
    if (enforce_large_target_group)
      saved_goal_mark.emplace_back(w->id, old_goal);
    ++issued;
  }
  if (enforce_large_target_group && gate_committed + issued < 3) {
    a.moves.resize(move_mark);
    planned_gold = gold_mark;
    for (const auto &entry : saved_goal_mark) {
      if (entry.second >= 0)
        large_goal_remember(entry.first, entry.second);
      else
        large_goal_clear(entry.first);
    }
    return false;
  }
  if (issued > 0) {
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              target);
    return true;
  }
  return false;
}

static bool add_late_split_capture_if_favorable(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int turn, int &forward_capture_target,
    std::set<int> &forward_capture_regions) {
  if (turn < 150)
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;
  int my_bases = count_my_bases(S, M);
  int enemy_bases = count_enemy_bases(S, M);
  if (enemy_bases <= 0 || my_bases <= enemy_bases)
    return false;
  if (minimum_staff_deficit(S, a, M) > 0)
    return false;

  int alive = count_my_alive(S, M) + a.train_n;
  int min_force = my_bases + (M.N >= 57 ? 20 : 12);
  if (alive < min_force)
    return false;

  forward_capture_target =
      select_forward_capture_target(S, M, P, forward_capture_target);
  if (forward_capture_target < 0)
    return false;
  const Building *target_building = find_building(S, forward_capture_target);
  if (target_building == nullptr || target_building->side == M.my_side ||
      target_building->type != BType::BASE)
    return false;

  forward_capture_regions.insert(forward_capture_target);
  int need = capture_attack_need(S, M, P, forward_capture_target);
  if (turn >= 170)
    need += M.N >= 57 ? 4 : 2;
  need = std::min(M.N >= 57 ? 18 : 14, std::max(6, need));
  return add_forward_capture_moves(S, M, P, a, planned_gold,
                                   forward_capture_target, need,
                                   forward_capture_regions);
}

static bool allow_favorable_hq3_pressure(const GameState &S, const GameMap &M,
                                         const Paths &P, const Actions &a,
                                         int planned_gold, int turn,
                                         int current_my_bases) {
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr || hq->level != 2)
    return false;
  if (turn < 75 || current_my_bases < 5)
    return false;
  if (planned_gold < HQ_LEVELS[3].upgrade_cost + TRAIN_COST)
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;
  int enemy_bases = count_enemy_bases(S, M);
  int my_bases = count_my_bases(S, M);
  bool enemy_bases_low = enemy_bases <= 5;
  bool favorable_count = my_bases >= enemy_bases + 2 && enemy_bases <= 7;
  bool strong_capture_pressure =
      count_forward_my_bases(S, M, P) > 0 && my_bases >= enemy_bases;
  return minimum_staff_deficit(S, a, M) == 0 &&
         (enemy_bases_low || favorable_count || strong_capture_pressure);
}

static bool add_hq_upgrade_when_enemy_bases_low(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, int turn,
    const Building *hq) {
  (void)P;
  if (hq == nullptr || hq->level >= HQ_MAX_LEVEL)
    return false;
  if (used_upgrades.count(hq->region))
    return false;
  if (count_enemy_bases(S, M) > 2)
    return false;
  int next_level = hq->level + 1;
  int cost = HQ_LEVELS[next_level].upgrade_cost;
  int reserve = turn < 175 ? TRAIN_COST : 0;
  if (planned_gold < cost + reserve)
    return false;
  return add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                              hq->region);
}

static bool add_captured_base_fill_moves(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, const std::set<int> &capture_regions) {
  struct Need {
    int region;
    int need;
    double score;
  };
  std::vector<Need> needs;
  for (int region : capture_regions) {
    const Building *b = find_building(S, region);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, region, M) > 0)
      continue;
    int required = large_strategy_active(M) ? large_base_staff_need(*b) : 1;
    int have = committed_my_count_at(S, a, region, M);
    int need = required - have;
    if (need <= 0)
      continue;
    double score = P.dist[M.my_hq][region] - b->level * 100.0;
    needs.push_back(Need{region, need, score});
  }
  std::sort(needs.begin(), needs.end(),
            [](const Need &lhs, const Need &rhs) {
              if (lhs.score != rhs.score)
                return lhs.score < rhs.score;
              return lhs.region < rhs.region;
            });

  bool issued = false;
  for (const Need &need : needs) {
    int still_needed = need.need;
    while (still_needed > 0) {
      std::vector<const Warrior *> candidates;
      for (const auto &w : S.warriors) {
        if (w.region == need.region)
          continue;
        if (!can_move_non_emergency(S, M, a, w))
          continue;
        if (is_stronghold(M, w.region) && find_building(S, w.region) == nullptr)
          continue;
        if (P.nxt[w.region][need.region] == -1)
          continue;
        if (capture_regions.count(w.region)) {
          const Building *src = find_building(S, w.region);
          if (src != nullptr && src->side == M.my_side &&
              src->type == BType::BASE) {
            int required = large_strategy_active(M) ? large_base_staff_need(*src) : 1;
            int after_departures = count_my_stationary_at(S, w.region, M) -
                                   planned_moves_from_region(a, S, w.region);
            if (after_departures <= required)
              continue;
          }
        }
        candidates.push_back(&w);
      }
      if (candidates.empty())
        break;
      std::sort(candidates.begin(), candidates.end(),
                [&](const Warrior *lhs, const Warrior *rhs) {
                  if (P.dist[lhs->region][need.region] !=
                      P.dist[rhs->region][need.region]) {
                    return P.dist[lhs->region][need.region] <
                           P.dist[rhs->region][need.region];
                  }
                  return lhs->id.num < rhs->id.num;
                });
      const Warrior *w = candidates.front();
      if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w,
                                        need.region))
        break;
      issued = true;
      --still_needed;
    }
  }
  return issued;
}

static int captured_base_worker_deficit(
    const GameState &S, const GameMap &M, const Actions &a,
    const std::set<int> &capture_regions) {
  int deficit = 0;
  for (int region : capture_regions) {
    const Building *b = find_building(S, region);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
      continue;
    int required = large_strategy_active(M) ? large_base_staff_need(*b) : 1;
    int have = committed_my_count_at(S, a, region, M);
    deficit += std::max(0, required - have);
  }
  return deficit;
}

static int planned_work_income_floor(const GameState &S, const GameMap &M,
                                     const Actions &a) {
  int income = 0;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side)
      continue;
    int workers = count_my_stationary_at(S, b.region, M) -
                  planned_moves_from_region(a, S, b.region);
    workers = std::max(0, workers);
    income += WORK_INCOME * std::min(workers, b.work_cap());
  }
  return income;
}

static int food_safe_gold_floor(const GameState &S, const GameMap &M,
                                const Actions &a, int turn) {
  int alive_after_train = count_my_alive(S, M) + a.train_n;
  int reserve_turns = std::min(3, std::max(1, MAX_TURN - turn + 1));
  int near_income = planned_work_income_floor(S, M, a) *
                    std::min(2, reserve_turns);
  int needed_food = alive_after_train * UPKEEP_PER_WARRIOR * reserve_turns;
  return std::max(30, needed_food - near_income + 30);
}

static bool can_leave_late_all_in_source(const GameState &S, const GameMap &M,
                                         const Actions &a, int region) {
  const Building *b = find_building(S, region);
  if (b == nullptr || b->side != M.my_side)
    return true;
  int after_departures =
      count_my_stationary_at(S, region, M) -
      planned_moves_from_region(a, S, region);
  int reserve = 0;
  if (b->type == BType::BASE) {
    reserve = large_strategy_active(M) ? large_base_staff_need(*b) : 1;
  } else {
    reserve = std::min(b->work_cap(), 2);
  }
  return after_departures > reserve;
}

static bool add_front_half_hq_pressure_under_emergency(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int max_moves = 99) {
  if (M.N <= 56)
    return false;
  bool issued = false;
  int moved = 0;
  for (const auto &w : S.warriors) {
    if (moved >= max_moves)
      break;
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (!should_keep_attacking_under_emergency(w, M))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, w, M.opp_hq))
      continue;
    ++moved;
    issued = true;
  }
  return issued;
}

static int recovery_attack_need(const GameState &S, const GameMap &M,
                                const Paths &P, int target) {
  const Building *b = find_building(S, target);
  if (b == nullptr)
    return 1;
  if (b->side == M.my_side || b->type != BType::BASE)
    return 0;
  int need = 4;
  need += count_enemy_warriors_at(S, target, M);
  need += enemy_near_region(S, M, P, target, 1) / 2;
  need += std::max(0, b->hp + 5) / 6;
  need += std::max(0, b->level - 1);
  return std::min(14, std::max(5, need));
}

static int select_low_base_recovery_target(
    const GameState &S, const GameMap &M, const Paths &P,
    const std::set<int> &ever_owned_base_regions, int current_target) {
  auto usable = [&](int region) {
    if (!ever_owned_base_regions.count(region))
      return false;
    if (!is_stronghold(M, region))
      return false;
    const Building *b = find_building(S, region);
    if (b != nullptr && b->side == M.my_side && b->type == BType::BASE)
      return false;
    return P.nxt[M.my_hq][region] != -1;
  };

  (void)current_target;

  int best = -1;
  double best_score = std::numeric_limits<double>::infinity();
  for (int region : ever_owned_base_regions) {
    if (!usable(region))
      continue;
    const Building *b = find_building(S, region);
    int nearest_hops = nearest_my_building_hops(S, M, P, region);
    if (nearest_hops > M.N)
      continue;
    double score = nearest_hops * 35.0 + P.hops[M.my_hq][region] * 3.0;
    if (b == nullptr) {
      score -= 120.0;
    } else if (b->side != M.my_side) {
      score += b->hp * 5.0 + b->level * 45.0;
      score += count_enemy_warriors_at(S, region, M) * 90.0;
      score += enemy_near_region(S, M, P, region, 1) * 35.0;
    }
    if (score < best_score) {
      best_score = score;
      best = region;
    }
  }
  return best;
}

static bool add_low_base_recovery_moves(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int target,
                                        int desired_count) {
  if (target < 0 || desired_count <= 0)
    return false;

  int committed = committed_my_count_at(S, a, target, M);
  int need = std::max(0, desired_count - committed);
  if (need <= 0)
    return false;

  std::vector<const Warrior *> candidates;
  const Building *hq = my_hq_building(S, M);
  for (const auto &w : S.warriors) {
    if (!can_move_non_emergency(S, M, a, w))
      continue;
    if (w.region == target)
      continue;
    if (is_stronghold(M, w.region) && find_building(S, w.region) == nullptr)
      continue;
    if (P.nxt[w.region][target] == -1)
      continue;
    if (w.region == M.my_hq && hq != nullptr) {
      int after_departures = count_my_stationary_at(S, M.my_hq, M) -
                             planned_moves_from_region(a, S, M.my_hq);
      int reserve = hq->work_cap() + (hq->level >= HQ_MAX_LEVEL ? 2 : 4);
      if (after_departures <= reserve)
        continue;
    }
    candidates.push_back(&w);
  }

  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              bool lhs_hq = lhs->region == M.my_hq;
              bool rhs_hq = rhs->region == M.my_hq;
              if (lhs_hq != rhs_hq)
                return lhs_hq > rhs_hq;
              if (P.dist[lhs->region][target] != P.dist[rhs->region][target])
                return P.dist[lhs->region][target] <
                       P.dist[rhs->region][target];
              return lhs->id.num < rhs->id.num;
            });

  int issued = 0;
  for (const Warrior *w : candidates) {
    if (issued >= need)
      break;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, target))
      continue;
    ++issued;
  }
  return issued > 0;
}

static bool apply_low_base_recovery_mode(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, int &planned_bases,
    int max_my_bases_seen, const std::set<int> &ever_owned_base_regions,
    int &recovery_target, const Building *hq) {
  int current_bases = count_my_bases(S, M);
  int recover_goal = std::min(TARGET_BASE_COUNT, max_my_bases_seen);
  if (current_bases > 3 || recover_goal < 4 || current_bases >= recover_goal)
    return false;

  for (int region : ever_owned_base_regions) {
    if (planned_bases >= recover_goal)
      break;
    const Building *b = find_building(S, region);
    if (b != nullptr)
      continue;
    if (!is_region_safe_for_build(S, M, region))
      continue;
    add_base_build(S, M, a, used_upgrades, planned_gold, planned_bases,
                   region);
  }

  recovery_target = select_low_base_recovery_target(
      S, M, P, ever_owned_base_regions, recovery_target);
  int attack_need = recovery_attack_need(S, M, P, recovery_target);
  if (recovery_target >= 0) {
    add_low_base_recovery_moves(S, M, P, a, planned_gold, recovery_target,
                                attack_need);
  }

  add_worker_fill_moves(S, M, P, a, planned_gold);

  if (hq != nullptr) {
    int desired_alive =
        hq->work_cap() + recover_goal + std::max(attack_need, 6) + 4;
    int wanted = std::max(0, desired_alive - count_my_alive(S, M) - a.train_n);
    int reserve_gold = 0;
    if (recovery_target >= 0) {
      const Building *target_building = find_building(S, recovery_target);
      if (target_building == nullptr ||
          target_building->side != M.my_side) {
        reserve_gold += BASE_LEVELS[1].cost;
      }
    }
    int train_gold = std::max(0, planned_gold - reserve_gold);
    if (wanted > 0 && train_gold >= TRAIN_COST) {
      int train_plan_gold = train_gold;
      int cap = HQ_LEVELS[hq->level].train_cap;
      add_train_if_needed(S, M, a, train_plan_gold,
                          std::min(cap, wanted));
      if (a.train_n > 0)
        planned_gold -= a.train_n * TRAIN_COST;
    }
  }

  return true;
}

static int select_hq_assault_rally_base(const GameState &S, const GameMap &M,
                                        const Paths &P) {
  int best = -1;
  int best_hops = M.N + 1;
  double best_dist = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, b.region, M) > 0)
      continue;
    if (P.nxt[b.region][M.opp_hq] == -1)
      continue;
    int hops = P.hops[b.region][M.opp_hq];
    double dist = P.dist[b.region][M.opp_hq];
    if (hops < best_hops || (hops == best_hops && dist < best_dist)) {
      best_hops = hops;
      best_dist = dist;
      best = b.region;
    }
  }
  return best;
}

static bool valid_hq_assault_rally_base(const GameState &S, const GameMap &M,
                                        const Paths &P, int region) {
  if (region < 0 || region >= M.N)
    return false;
  const Building *b = find_building(S, region);
  return b != nullptr && b->side == M.my_side && b->type == BType::BASE &&
         count_enemy_warriors_at(S, region, M) == 0 &&
         P.nxt[region][M.opp_hq] != -1;
}

static int hq_assault_launch_threshold(const GameMap &M, int turn) {
  if (M.N <= 56) {
    if (turn >= 170)
      return 3;
    if (turn >= 145)
      return 4;
    return 6;
  }
  if (turn >= 185)
    return 6;
  if (turn >= 160)
    return 9;
  if (turn >= 140)
    return 11;
  return 16;
}

struct HqAssaultRequirement {
  double defense_power = 0.0;
  int required_hp = 0;
  int required_attackers = 0;
  int enemy_hq_count = 0;
  int travel_hops = 0;
};

static int side_hp_at_region(const GameState &S, Side side, int region) {
  int hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side == side && w.region == region)
      hp += std::max(1, w.hp);
  }
  return hp;
}

[[maybe_unused]] static int side_count_within_hops(
    const GameState &S, const Paths &P, Side side, int center, int radius,
    bool exclude_center) {
  int count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != side)
      continue;
    if (exclude_center && w.region == center)
      continue;
    if (P.hops[w.region][center] <= radius)
      ++count;
  }
  return count;
}

static int side_hp_within_hops(const GameState &S, const Paths &P, Side side,
                               int center, int radius, bool exclude_center) {
  int hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != side)
      continue;
    if (exclude_center && w.region == center)
      continue;
    if (P.hops[w.region][center] <= radius)
      hp += std::max(1, w.hp);
  }
  return hp;
}

static int enemy_route_hp_to_hq(const GameState &S, const GameMap &M,
                                const Paths &P, int rally_region) {
  Side enemy = opposite(M.my_side);
  int hp = 0;
  int cur = rally_region;
  std::set<int> seen;
  for (int step = 0; step <= M.N && cur != M.opp_hq; ++step) {
    if (cur < 0 || cur >= M.N || seen.count(cur))
      break;
    seen.insert(cur);
    int nxt = P.nxt[cur][M.opp_hq];
    if (nxt < 0)
      break;
    cur = nxt;
    if (cur != M.opp_hq)
      hp += side_hp_at_region(S, enemy, cur);
  }
  return hp;
}

static HqAssaultRequirement compute_hq_assault_requirement(
    const GameState &S, const GameMap &M, const Paths &P, int rally_region,
    int turn, int min_attackers, double avg_attacker_hp) {
  Side enemy = opposite(M.my_side);
  const Building *enemy_hq = hq_building_of(S, M, enemy);
  int enemy_hq_level =
      enemy_hq == nullptr ? 1 : std::max(1, std::min(HQ_MAX_LEVEL, enemy_hq->level));
  int enemy_hq_hp =
      enemy_hq == nullptr ? HQ_LEVELS[enemy_hq_level].hp : enemy_hq->hp;

  int travel_hops = P.hops[rally_region][M.opp_hq];
  if (travel_hops > M.N)
    travel_hops = M.N;
  int remaining_turns = std::max(0, MAX_TURN - turn + 1);
  int predicted_turns = std::min(travel_hops, remaining_turns);

  int near_radius = M.N >= 57 ? 2 : 2;
  int enemy_hq_count = count_enemy_warriors_at(S, M.opp_hq, M);
  int enemy_hq_hp_sum = side_hp_at_region(S, enemy, M.opp_hq);
  int enemy_near_hp =
      side_hp_within_hops(S, P, enemy, M.opp_hq, near_radius, true);
  int route_hp = enemy_route_hp_to_hq(S, M, P, rally_region);

  constexpr double kHqHpWeight = 0.60;
  constexpr double kTurretWeight = 0.75;
  constexpr double kNearWeight = 0.50;
  constexpr double kPredictedTrainWeight = 0.50;
  constexpr double kRouteEnemyWeight = 0.35;

  double predicted_enemy_train_hp =
      static_cast<double>(predicted_turns) *
      HQ_LEVELS[enemy_hq_level].train_cap *
      HQ_LEVELS[enemy_hq_level].warrior_hp * kPredictedTrainWeight;
  double defense_power =
      static_cast<double>(enemy_hq_hp_sum) +
      static_cast<double>(enemy_near_hp) * kNearWeight +
      static_cast<double>(enemy_hq_hp) * kHqHpWeight +
      static_cast<double>(HQ_LEVELS[enemy_hq_level].turret) *
          std::max(1, travel_hops) * kTurretWeight +
      predicted_enemy_train_hp +
      static_cast<double>(route_hp) * kRouteEnemyWeight;

  double safety_ratio = M.N >= 57 ? 1.00 : 1.18;
  if (turn >= 190)
    safety_ratio -= 0.18;
  else if (turn >= 175)
    safety_ratio -= 0.10;
  safety_ratio = std::max(0.82, safety_ratio);

  int required_hp = static_cast<int>(std::ceil(defense_power * safety_ratio));
  double avg_hp = std::max(1.0, avg_attacker_hp);
  int required_by_hp = static_cast<int>(std::ceil(required_hp / avg_hp));
  int required_attackers =
      std::max({min_attackers, enemy_hq_count + 2, required_by_hp});

  return HqAssaultRequirement{defense_power, required_hp, required_attackers,
                              enemy_hq_count, travel_hops};
}

static int count_hq_assault_ready_at(const GameState &S, const GameMap &M,
                                     const Actions &a, int rally_region) {
  int count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region != rally_region || warrior_already_planned(a, w.id))
      continue;
    ++count;
  }
  return count;
}

static int count_hq_assault_inbound_to(const GameState &S, const GameMap &M,
                                       int rally_region) {
  int count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::MOVING &&
        w.target == rally_region) {
      ++count;
    }
  }
  return count;
}

static int hq_assault_rally_lock_floor(const GameMap &M, int turn) {
  if (M.N <= 56)
    return turn >= 120 ? 4 : 5;
  if (turn >= 150)
    return 8;
  return 16;
}

static void refresh_hq_assault_rally_state(const GameState &S,
                                           const GameMap &M,
                                           const Paths &P, int turn) {
  if (turn <= 1) {
    g_hq_assault_rally_region = -1;
    g_hq_assault_committed = false;
  }
  if (valid_hq_assault_rally_base(S, M, P, g_hq_assault_rally_region))
    return;
  g_hq_assault_rally_region = select_hq_assault_rally_base(S, M, P);
  g_hq_assault_committed = false;
}

static bool prime_hq_assault_rally_lock(const GameState &S,
                                        const GameMap &M, const Paths &P,
                                        const Actions &a, int turn) {
  refresh_hq_assault_rally_state(S, M, P, turn);
  int rally_region = g_hq_assault_rally_region;
  if (rally_region < 0)
    return false;
  int ready = count_hq_assault_ready_at(S, M, a, rally_region);
  int inbound = count_hq_assault_inbound_to(S, M, rally_region);
  if (ready + inbound < hq_assault_rally_lock_floor(M, turn))
    return false;
  g_hq_assault_committed = true;
  return true;
}

static bool enemy_main_left_hq_for_race(const GameState &S,
                                        const GameMap &M, const Paths &P) {
  int enemy_hq_count = count_enemy_warriors_at(S, M.opp_hq, M);
  int hq_limit = M.N <= 56 ? 5 : 8;
  if (enemy_hq_count > hq_limit)
    return false;
  int pressure_radius = M.N <= 56 ? 3 : 4;
  int pressure_need = M.N <= 56 ? 4 : 10;
  int enemy_pressure = enemy_near_region(S, M, P, M.my_hq, pressure_radius);
  if (count_enemy_warriors_at(S, M.my_hq, M) > 0)
    enemy_pressure += pressure_need;
  return enemy_pressure >= pressure_need;
}

static int hq_race_launch_floor(const GameMap &M, int turn) {
  if (M.N <= 56)
    return turn >= 150 ? 3 : 4;
  if (turn >= 190)
    return 8;
  if (turn >= 175)
    return 9;
  return 12;
}

static bool add_forced_hq_race_launch_if_ready(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int turn) {
  bool small_late_force = M.N <= 56 && turn >= 115;
  bool large_late_force = large_strategy_active(M) && turn >= 190;
  if (!small_late_force && !large_late_force &&
      !enemy_main_left_hq_for_race(S, M, P))
    return false;
  refresh_hq_assault_rally_state(S, M, P, turn);
  int rally_region = g_hq_assault_rally_region;
  if (rally_region < 0)
    return false;

  int ready = count_hq_assault_ready_at(S, M, a, rally_region);
  int reserve = reserve_need_at_region(S, M, rally_region);
  int launchable = std::max(0, ready - reserve);
  int threshold = hq_race_launch_floor(M, turn);
  if (launchable < threshold)
    return false;

  std::vector<const Warrior *> attackers;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region != rally_region || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    attackers.push_back(&w);
  }
  std::sort(attackers.begin(), attackers.end(),
            [](const Warrior *lhs, const Warrior *rhs) {
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  int issued = 0;
  for (const Warrior *w : attackers) {
    if (issued >= launchable)
      break;
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, M.opp_hq))
      continue;
    ++issued;
  }
  if (issued <= 0)
    return false;
  g_hq_assault_committed = true;
  g_hq_assault_rally_region = -1;
  return true;
}

static bool add_hq_assault_launch_moves(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int turn,
                                        int rally_region, int threshold) {
  if (rally_region < 0)
    return false;
  int ready = count_hq_assault_ready_at(S, M, a, rally_region);
  int reserve = reserve_need_at_region(S, M, rally_region);
  int launchable = std::max(0, ready - reserve);
  if (launchable < threshold)
    return false;

  std::vector<const Warrior *> attackers;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region != rally_region || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    attackers.push_back(&w);
  }
  std::sort(attackers.begin(), attackers.end(),
            [](const Warrior *lhs, const Warrior *rhs) {
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  int attack_hp = 0;
  int considered = std::min<int>(launchable, static_cast<int>(attackers.size()));
  for (int i = 0; i < considered; ++i)
    attack_hp += std::max(1, attackers[i]->hp);
  double avg_attacker_hp =
      considered > 0 ? static_cast<double>(attack_hp) / considered
                     : static_cast<double>(HQ_LEVELS[1].warrior_hp);
  HqAssaultRequirement req = compute_hq_assault_requirement(
      S, M, P, rally_region, turn, threshold, avg_attacker_hp);
  bool late_large_score_pressure =
      large_strategy_active(M) && turn >= 183 && launchable >= 16 && attack_hp >= 95 &&
      static_cast<double>(attack_hp) >=
          static_cast<double>(req.required_hp) * 0.34;
#ifdef ASSAULT_DEBUG
  if (M.N >= 90 && turn >= 145) {
    std::cerr << "ASSAULT turn=" << turn << " rally=" << rally_region
              << " ready=" << ready << " reserve=" << reserve
              << " launchable=" << launchable << " hp=" << attack_hp
              << " req_hp=" << req.required_hp
              << " req_cnt=" << req.required_attackers
              << " late=" << late_large_score_pressure << "\n";
  }
#endif
  if (!late_large_score_pressure &&
      (launchable < req.required_attackers || attack_hp < req.required_hp))
    return false;

  bool issued = false;
  int issued_count = 0;
  for (const Warrior *w : attackers) {
    if (issued_count >= launchable)
      break;
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    int routed_target = large_waypoint_or_target(S, M, P, w->region, M.opp_hq);
    int cost = move_cost_to(S, M, routed_target);
    if (planned_gold - cost < food_safe_gold_floor(S, M, a, turn))
      break;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, M.opp_hq))
      continue;
    issued = true;
    ++issued_count;
  }
  return issued;
}

static bool add_hq_assault_gather_moves(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int rally_region,
                                        int max_moves) {
  if (rally_region < 0 || max_moves <= 0)
    return false;

  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == rally_region || w.region == M.opp_hq)
      continue;
    if (warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][rally_region] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    candidates.push_back(&w);
  }

  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][rally_region] !=
                  P.hops[rhs->region][rally_region]) {
                return P.hops[lhs->region][rally_region] <
                       P.hops[rhs->region][rally_region];
              }
              if (P.dist[lhs->region][rally_region] !=
                  P.dist[rhs->region][rally_region]) {
                return P.dist[lhs->region][rally_region] <
                       P.dist[rhs->region][rally_region];
              }
              return lhs->id.num < rhs->id.num;
            });

  int issued = 0;
  for (const Warrior *w : candidates) {
    if (issued >= max_moves)
      break;
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w,
                                      rally_region))
      continue;
    ++issued;
  }
  return issued > 0;
}

static bool add_staged_hq_assault_moves(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int turn,
                                        bool allow_idle_hold = true) {
  static int sticky_rally_region = -1;
  if (turn <= 1) {
    sticky_rally_region = -1;
    g_hq_assault_rally_region = -1;
  }
  if (!valid_hq_assault_rally_base(S, M, P, sticky_rally_region))
    sticky_rally_region = select_hq_assault_rally_base(S, M, P);

  int rally_region = sticky_rally_region;
  g_hq_assault_rally_region = rally_region;
  if (rally_region < 0)
    return false;

  int threshold = hq_assault_launch_threshold(M, turn);
  if (add_hq_assault_launch_moves(S, M, P, a, planned_gold, turn,
                                  rally_region, threshold)) {
    sticky_rally_region = -1;
    g_hq_assault_rally_region = -1;
    return true;
  }

  int ready = count_hq_assault_ready_at(S, M, a, rally_region);
  int inbound = count_hq_assault_inbound_to(S, M, rally_region);
  int committed_hp = 0;
  int committed_count = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    bool committed =
        (w.state == WState::STATIONARY && w.region == rally_region &&
         !warrior_already_planned(a, w.id)) ||
        (w.state == WState::MOVING && w.target == rally_region);
    if (!committed)
      continue;
    committed_hp += std::max(1, w.hp);
    ++committed_count;
  }
  const Building *my_hq = my_hq_building(S, M);
  int fallback_hp = my_hq == nullptr
                        ? HQ_LEVELS[1].warrior_hp
                        : HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL,
                                                          my_hq->level))]
                              .warrior_hp;
  double avg_hp = committed_count > 0
                      ? static_cast<double>(committed_hp) / committed_count
                      : static_cast<double>(fallback_hp);
  HqAssaultRequirement req = compute_hq_assault_requirement(
      S, M, P, rally_region, turn, threshold, avg_hp);
  int gather_need =
      std::max(0, req.required_attackers - ready - inbound);
  int max_gather = M.N <= 56 ? 8 : 12;
  if (add_hq_assault_gather_moves(S, M, P, a, planned_gold, rally_region,
                                  std::min(max_gather, gather_need))) {
    return true;
  }

  int hold_floor =
      M.N <= 56 ? std::max(2, req.required_attackers / 2)
                : std::max(6, (req.required_attackers * 2 + 2) / 3);
  return allow_idle_hold && ready + inbound >= hold_floor;
}

[[maybe_unused]] static bool add_large_map_prelaunch_gather_moves(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int turn) {
  if (M.N < 90 || turn < 155 || turn > 180)
    return false;
  int rally_region = select_hq_assault_rally_base(S, M, P);
  if (rally_region < 0)
    return false;
  int ready = count_hq_assault_ready_at(S, M, a, rally_region);
  int inbound = count_hq_assault_inbound_to(S, M, rally_region);
  int target_group = 28;
  int gather_need = std::max(0, target_group - ready - inbound);
  if (gather_need <= 0)
    return false;
  return add_hq_assault_gather_moves(S, M, P, a, planned_gold, rally_region,
                                     std::min(12, gather_need));
}

static bool add_optional_rebuild_lost_bases(
    const GameState &S, const GameMap &M, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, int &planned_bases,
    const std::set<int> &ever_owned_base_regions) {
  bool issued = false;
  int reserve_gold = M.N >= 57 ? 1000 : 700;
  for (int region : ever_owned_base_regions) {
    if (planned_gold < BASE_LEVELS[1].cost + reserve_gold)
      break;
    if (used_upgrades.count(region))
      continue;
    if (!is_stronghold(M, region))
      continue;
    if (find_building(S, region) != nullptr)
      continue;
    if (!is_region_safe_for_build(S, M, region))
      continue;
    if (add_base_build(S, M, a, used_upgrades, planned_gold, planned_bases,
                       region)) {
      issued = true;
    }
  }
  return issued;
}

static bool is_large_macro_recovery_region(const GameState &S,
                                           const GameMap &M, const Paths &P,
                                           int region) {
  if (M.N < 90 || !is_stronghold(M, region))
    return false;
  std::vector<int> targets = log2_target_order(S, M, P);
  return std::find(targets.begin(), targets.end(), region) != targets.end() ||
         is_front_half_region_for_my_side(M, region);
}

static bool large_macro_recovery_needed(
    const GameState &S, const GameMap &M, const Paths &P,
    int max_my_bases_seen, const std::set<int> &ever_owned_base_regions) {
  if (M.N < 90 || max_my_bases_seen < 6)
    return false;
  int current_bases = count_my_bases(S, M);
  int recover_goal = std::min(TARGET_BASE_COUNT, max_my_bases_seen);
  if (current_bases + 1 < recover_goal)
    return true;
  for (int region : ever_owned_base_regions) {
    if (!is_large_macro_recovery_region(S, M, P, region))
      continue;
    const Building *b = find_building(S, region);
    if (b == nullptr || b->side != M.my_side)
      return true;
  }
  return false;
}

static bool add_large_limited_macro_recovery(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, int &planned_bases,
    int max_my_bases_seen, const std::set<int> &ever_owned_base_regions,
    int &recovery_target, const Building *hq) {
  if (!large_macro_recovery_needed(S, M, P, max_my_bases_seen,
                                   ever_owned_base_regions))
    return false;

  bool issued = false;
  int recover_goal = std::min(TARGET_BASE_COUNT, max_my_bases_seen);
  for (int region : ever_owned_base_regions) {
    if (planned_bases >= recover_goal)
      break;
    if (!is_large_macro_recovery_region(S, M, P, region))
      continue;
    if (planned_gold < BASE_LEVELS[1].cost + 500)
      break;
    if (used_upgrades.count(region))
      continue;
    if (!is_region_safe_for_build(S, M, region))
      continue;
    if (find_building(S, region) != nullptr)
      continue;
    if (committed_my_count_at(S, a, region, M) <= 0)
      continue;
    if (add_base_build(S, M, a, used_upgrades, planned_gold, planned_bases,
                       region)) {
      issued = true;
    }
  }

  if (recovery_target < 0) {
    double best_score = std::numeric_limits<double>::infinity();
    for (int region : ever_owned_base_regions) {
      if (!is_large_macro_recovery_region(S, M, P, region))
        continue;
      const Building *b = find_building(S, region);
      if (b != nullptr && b->side == M.my_side)
        continue;
      if (P.nxt[M.my_hq][region] == -1)
        continue;
      double score = P.hops[M.my_hq][region] * 20.0 +
                     P.hops[region][M.opp_hq] * 2.0;
      if (b != nullptr && b->side != M.my_side)
        score += b->hp * 8.0 + count_enemy_warriors_at(S, region, M) * 80.0;
      if (score < best_score) {
        best_score = score;
        recovery_target = region;
      }
    }
  } else {
    const Building *b = find_building(S, recovery_target);
    if (b != nullptr && b->side == M.my_side)
      recovery_target = -1;
  }

  if (recovery_target >= 0) {
    const Building *b = find_building(S, recovery_target);
    int desired = (b != nullptr && b->side != M.my_side)
                      ? std::min(8, recovery_attack_need(S, M, P,
                                                         recovery_target))
                      : 2;
    if (add_low_base_recovery_moves(S, M, P, a, planned_gold,
                                    recovery_target, desired)) {
      issued = true;
    }
  }

  if (large_base_level_staff_deficit(S, a, M) > 0 &&
      add_worker_fill_moves(S, M, P, a, planned_gold)) {
    issued = true;
  }

  if (hq != nullptr) {
    int desired_alive =
        hq->work_cap() + recover_goal * 2 +
        (recovery_target >= 0 ? 6 : 0);
    int wanted = std::max(0, desired_alive - count_my_alive(S, M) - a.train_n);
    if (wanted > 0) {
      int cap = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].train_cap;
      int train_gold = std::max(0, planned_gold - BASE_LEVELS[1].cost);
      if (train_gold >= TRAIN_COST) {
        int train_plan_gold = train_gold;
        add_train_if_needed(S, M, a, train_plan_gold,
                            std::min(cap, wanted));
        if (a.train_n > 0) {
          planned_gold -= a.train_n * TRAIN_COST;
          issued = true;
        }
      }
    }
  }

  return issued;
}

static bool large_hq_pressure_feasible(const GameState &S, const GameMap &M,
                                       const Paths &P, const Actions &a,
                                       int turn) {
  if (!large_strategy_active(M))
    return true;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;
  const Building *my_hq = my_hq_building(S, M);
  if (my_hq == nullptr || my_hq->level < HQ_MAX_LEVEL)
    return false;
  if (large_base_level_staff_deficit(S, a, M) > 0 && turn < 195)
    return false;
  int enemy_bases = count_enemy_bases(S, M);
  if (enemy_bases > 2 && turn < 195)
    return false;

  int hq_path = P.hops[M.my_hq][M.opp_hq];
  if (hq_path > M.N)
    return false;
  int route_blockers = 0;
  Side enemy = opposite(M.my_side);
  for (const auto &b : S.buildings) {
    if (b.side != enemy || b.type != BType::BASE)
      continue;
    bool on_route = P.hops[M.my_hq][b.region] + P.hops[b.region][M.opp_hq] <=
                    hq_path + 1;
    bool near_enemy_hq = P.hops[b.region][M.opp_hq] <= 3;
    if ((on_route || near_enemy_hq) && b.hp > 4)
      ++route_blockers;
  }
  if (route_blockers > 0)
    return false;

  int attackers = 0;
  int attack_hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    ++attackers;
    attack_hp += std::max(1, w.hp);
  }

  int min_attackers = turn < 185 ? 18 : 12;
  if (attackers < min_attackers)
    return false;

  int enemy_hq_defenders = 0;
  int enemy_hq_defender_hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != enemy)
      continue;
    if (P.hops[w.region][M.opp_hq] <= 1) {
      ++enemy_hq_defenders;
      enemy_hq_defender_hp += std::max(1, w.hp);
    }
  }
  const Building *enemy_hq = find_building(S, M.opp_hq);
  int enemy_hq_level =
      enemy_hq == nullptr ? 1 : std::max(1, std::min(HQ_MAX_LEVEL,
                                                     enemy_hq->level));
  int enemy_hq_hp = enemy_hq == nullptr ? HQ_LEVELS[enemy_hq_level].hp
                                        : enemy_hq->hp;
  int turret_buffer = HQ_LEVELS[enemy_hq_level].turret *
                      std::max(4, P.hops[M.my_hq][M.opp_hq] / 5);
  int required_hp = enemy_hq_defender_hp + enemy_hq_hp + turret_buffer +
                    enemy_hq_defenders * 2;
  return attack_hp >= required_hp;
}

static bool add_decisive_hq_push_if_ready(const GameState &S, const GameMap &M,
                                          const Paths &P, Actions &a,
                                          int &planned_gold, int turn) {
  if (!large_hq_pressure_feasible(S, M, P, a, turn))
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;

  std::vector<const Warrior *> candidates;
  int available_force = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    candidates.push_back(&w);
    available_force += std::max(1, w.hp);
  }
  if (candidates.empty())
    return false;

  int enemy_bases = count_enemy_bases(S, M);
  double enemy_estimate = enemy_hq_defense_estimate(S, M, P);
  bool all_bases_cleared = enemy_bases == 0 && turn >= 120;
  bool strategic_finish =
      enemy_bases <= 8 && turn >= 115 &&
      static_cast<int>(candidates.size()) >= 6;
  bool decisive = turn >= 105 &&
                  static_cast<double>(available_force) >= enemy_estimate * 0.70 &&
                  static_cast<int>(candidates.size()) >= 6;
  bool large_force_window =
      M.N >= 57 && turn >= 125 && static_cast<int>(candidates.size()) >= 10 &&
      static_cast<double>(available_force) >= enemy_estimate * 0.60;
  bool small_late_hq_pressure =
      M.N <= 56 && turn >= 130 && static_cast<int>(candidates.size()) >= 2;
  bool large_hq5_late_pressure =
      M.N >= 57 && turn >= 140 && static_cast<int>(candidates.size()) >= 6;
  if (!all_bases_cleared && !strategic_finish && !decisive &&
      !large_force_window &&
      !small_late_hq_pressure && !large_hq5_late_pressure)
    return false;

  bool issued = add_staged_hq_assault_moves(S, M, P, a, planned_gold, turn,
                                            turn >= 140);
  if (issued)
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  return issued;
}

static bool add_large_distributed_hq_pressure_if_ready(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int turn) {
  if (!large_strategy_active(M) || turn < 160)
    return false;
  if (!large_hq_pressure_feasible(S, M, P, a, turn))
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;

  std::vector<const Warrior *> candidates;
  int force_hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    candidates.push_back(&w);
    force_hp += std::max(1, w.hp);
  }
  int min_count = turn < 175 ? 26 : 22;
  int min_hp = turn < 175 ? 160 : 140;
  if (static_cast<int>(candidates.size()) < min_count || force_hp < min_hp)
    return false;

  double enemy_estimate = enemy_hq_defense_estimate(S, M, P);
  double required_ratio = turn < 175 ? 1.00 : 0.75;
  if (static_cast<double>(force_hp) < enemy_estimate * required_ratio)
    return false;

  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][M.opp_hq] !=
                  P.hops[rhs->region][M.opp_hq]) {
                return P.hops[lhs->region][M.opp_hq] <
                       P.hops[rhs->region][M.opp_hq];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  bool issued = false;
  for (const Warrior *w : candidates) {
    int routed_target = large_waypoint_or_target(S, M, P, w->region, M.opp_hq);
    int cost = move_cost_to(S, M, routed_target);
    if (planned_gold - cost < food_safe_gold_floor(S, M, a, turn))
      break;
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, M.opp_hq))
      continue;
    issued = true;
  }
  if (issued)
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  return issued;
}

static bool add_low_enemy_base_hq_pressure(const GameState &S, const GameMap &M,
                                           const Paths &P, Actions &a,
                                           int &planned_gold, int turn) {
  if (turn < 110)
    return false;
  if (!large_hq_pressure_feasible(S, M, P, a, turn))
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;

  int enemy_bases = count_enemy_bases(S, M);
  int my_bases = count_my_bases(S, M);
  bool large_map = large_strategy_active(M);
  if (!large_map && M.N >= 57 && turn < 170)
    return false;
  int low_base_limit = large_map ? 1 : 2;
  int late_base_limit = large_map ? 3 : 4;
  bool low_enemy_bases = enemy_bases <= low_base_limit && turn >= 110;
  bool late_score_pressure =
      enemy_bases <= late_base_limit && my_bases >= enemy_bases && turn >= 135;
  bool final_turn_pressure = enemy_bases <= late_base_limit + 2 && turn >= 185;
  if (!low_enemy_bases && !late_score_pressure && !final_turn_pressure)
    return false;

  std::vector<const Warrior *> attackers;
  int hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    attackers.push_back(&w);
    hp += std::max(1, w.hp);
  }

  int min_count = large_map ? 10 : 5;
  if (turn >= 170)
    min_count = large_map ? 7 : 3;
  if (turn >= 188)
    min_count = large_map ? 5 : 2;
  if (enemy_bases <= 1)
    min_count = std::min(min_count, large_map ? 5 : 2);
  if (static_cast<int>(attackers.size()) < min_count && hp < min_count * 4)
    return false;

  std::sort(attackers.begin(), attackers.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][M.opp_hq] !=
                  P.hops[rhs->region][M.opp_hq]) {
                return P.hops[lhs->region][M.opp_hq] <
                       P.hops[rhs->region][M.opp_hq];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  bool issued = false;
  for (const Warrior *w : attackers) {
    int routed_target = large_waypoint_or_target(S, M, P, w->region, M.opp_hq);
    int cost = move_cost_to(S, M, routed_target);
    if (turn < 190 && planned_gold - cost < food_safe_gold_floor(S, M, a, turn))
      break;
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, M.opp_hq))
      continue;
    issued = true;
  }
  if (issued) {
    g_hq_assault_committed = true;
    g_hq_assault_rally_region = -1;
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  }
  return issued;
}

static bool add_late_direct_hq_pressure(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int turn) {
  bool large_map = large_strategy_active(M);
  int start_turn = large_map ? 165 : (M.N >= 57 ? 170 : 115);
  if (turn < start_turn)
    return false;
  if (!large_hq_pressure_feasible(S, M, P, a, turn))
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;

  int my_bases = count_my_bases(S, M);
  int alive = count_my_alive(S, M) + a.train_n;
  if (large_map) {
    if (my_bases < 5 && alive < 20)
      return false;
  } else {
    if (my_bases < 3 && alive < 10)
      return false;
  }

  std::vector<const Warrior *> attackers;
  int hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    attackers.push_back(&w);
    hp += std::max(1, w.hp);
  }

  int min_count = large_map ? 8 : 3;
  if (!large_map && turn >= 140)
    min_count = 2;
  if (turn >= 180)
    min_count = large_map ? 5 : 2;
  if (static_cast<int>(attackers.size()) < min_count && hp < min_count * 4)
    return false;

  std::sort(attackers.begin(), attackers.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][M.opp_hq] !=
                  P.hops[rhs->region][M.opp_hq]) {
                return P.hops[lhs->region][M.opp_hq] <
                       P.hops[rhs->region][M.opp_hq];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  bool issued = false;
  for (const Warrior *w : attackers) {
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, M.opp_hq))
      continue;
    issued = true;
  }
  if (issued) {
    g_hq_assault_committed = true;
    g_hq_assault_rally_region = -1;
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  }
  return issued;
}

static bool add_late_total_all_in_moves(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        int &planned_gold, int turn) {
  if (turn < 190 || count_enemy_bases(S, M) > 1)
    return false;
  if (!large_hq_pressure_feasible(S, M, P, a, turn))
    return false;
  bool issued = add_staged_hq_assault_moves(S, M, P, a, planned_gold, turn);
  if (issued)
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  return issued;
}

static bool add_small_forced_hq_race_launch_if_ready(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int turn) {
  if (M.N > 56 || turn < 115)
    return false;

  std::vector<const Warrior *> attackers;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    attackers.push_back(&w);
  }

  int threshold = turn >= 170 ? 3 : 4;
  if (static_cast<int>(attackers.size()) < threshold)
    return false;

  std::sort(attackers.begin(), attackers.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][M.opp_hq] !=
                  P.hops[rhs->region][M.opp_hq]) {
                return P.hops[lhs->region][M.opp_hq] <
                       P.hops[rhs->region][M.opp_hq];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  bool issued = false;
  for (const Warrior *w : attackers) {
    int cost = move_cost_to(S, M, M.opp_hq);
    if (planned_gold < cost)
      break;
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    a.moves.emplace_back(w->id, M.opp_hq);
    planned_gold -= cost;
    issued = true;
  }
  if (issued) {
    g_hq_assault_rally_region = -1;
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  }
  return issued;
}

static bool apply_small_map_hq_approach_defense(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, const Building *hq) {
  if (M.N > 56 || hq == nullptr)
    return false;
  int close = enemy_near_region(S, M, P, M.my_hq, 3);
  int near = enemy_near_region(S, M, P, M.my_hq, 4);
  if (close == 0 && near < 2)
    return false;

  add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);

  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (!should_recall_for_emergency(w, M))
      continue;
    if (large_strategy_active(M) && large_final_goal_useful(S, M, large_goal_saved(w.id)))
      continue;
    if (w.region == M.my_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.my_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    int cost = move_cost_to(S, M, M.my_hq);
    if (planned_gold < cost)
      break;
    a.moves.emplace_back(w.id, M.my_hq);
    planned_gold -= cost;
  }
  add_front_half_hq_pressure_under_emergency(S, M, P, a, planned_gold);

  int cap = HQ_LEVELS[hq->level].train_cap;
  add_train_if_needed(S, M, a, planned_gold, cap);
  return !a.moves.empty() || !a.upgrades.empty() || a.train_n > 0;
}

static bool target_macro_complete(const GameState &S, const Actions &a,
                                  const GameMap &M, const Paths &P) {
  const Building *hq = my_hq_building(S, M);
  int goal = active_macro_target_goal(S, M, P);
  int level1_goal = std::min(goal, 6);
  return hq != nullptr && count_target_bases_built(S, M, P) >= level1_goal &&
         target_base_worker_deficit(S, a, M, P) == 0;
}

static bool add_target_base_fill_moves(const GameState &S, const GameMap &M,
                                       const Paths &P, Actions &a,
                                       int &planned_gold, int max_moves,
                                       int preupgrade_region = -1) {
  struct Need {
    int region;
    int need;
    double score;
  };
  std::vector<Need> needs;
  for (int r : log2_target_order(S, M, P)) {
    const Building *b = find_building(S, r);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, r, M) > 0)
      continue;
    int need = (b->level == 1 && r == preupgrade_region)
                   ? 2
                   : std::max(1, std::min(BASE_MAX_LEVEL, b->level));
    int have = committed_my_count_at(S, a, r, M);
    if (have < need) {
      double score = (b->level >= 2 ? -1000.0 : 0.0) + P.dist[M.my_hq][r];
      needs.push_back(Need{r, need - have, score});
    }
  }
  std::sort(needs.begin(), needs.end(), [](const Need &lhs, const Need &rhs) {
    if (lhs.score != rhs.score)
      return lhs.score < rhs.score;
    return lhs.region < rhs.region;
  });

  bool issued = false;
  int issued_count = 0;
  for (const Need &need : needs) {
    int still_needed = need.need;
    while (still_needed > 0 && issued_count < max_moves &&
           add_surplus_moves_to_region(S, M, P, a, planned_gold, need.region,
                                       1, preupgrade_region, 2)) {
      issued = true;
      --still_needed;
      ++issued_count;
    }
    if (issued_count >= max_moves)
      break;
  }
  return issued;
}

static bool add_worker_move_to_target(const GameState &S, const GameMap &M,
                                      const Paths &P, Actions &a,
                                      int &planned_gold, int target,
                                      bool keep_build_reserve,
                                      int protected_region = -1,
                                      int protected_need = 0) {
  (void)keep_build_reserve;
  if (target < 0 || target >= M.N)
    return false;
  if (P.nxt[M.my_hq][target] == -1)
    return false;

  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (!can_move_non_emergency(S, M, a, w))
      continue;
    if (is_stronghold(M, w.region) && find_building(S, w.region) == nullptr &&
        !enemy_building_at(S, M, w.region))
      continue;
    if (P.nxt[w.region][target] == -1)
      continue;
    if (would_pull_forward_pressure_back(M, P, w.region, target))
      continue;
    if (w.region == protected_region) {
      int after_departures =
          count_my_stationary_at(S, w.region, M) -
          planned_moves_from_region(a, S, w.region);
      if (after_departures <= protected_need)
        continue;
    }
    candidates.push_back(&w);
  }
  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              bool lhs_hq = lhs->region == M.my_hq;
              bool rhs_hq = rhs->region == M.my_hq;
              if (lhs_hq != rhs_hq)
                return lhs_hq > rhs_hq;
              if (P.dist[lhs->region][target] != P.dist[rhs->region][target])
                return P.dist[lhs->region][target] <
                       P.dist[rhs->region][target];
              return lhs->id.num < rhs->id.num;
            });

  for (const Warrior *w : candidates) {
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, target))
      continue;
    return true;
  }
  return false;
}

static bool apply_large_map_hq_approach_defense(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, const Building *hq) {
  if (M.N <= 56 || hq == nullptr)
    return false;

  int close = enemy_near_region(S, M, P, M.my_hq, 1);
  int near = enemy_near_region(S, M, P, M.my_hq, 2);
  if (close == 0 && near < 4)
    return false;
  if (!hq_assault_urgent_threat_active(S, M, P))
    return false;

  bool issued = false;
  int max_hq_hp = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].hp;
  bool can_upgrade_hq_for_defense = !(M.N < 90 && hq->level >= 3);
  if (can_upgrade_hq_for_defense &&
      (close >= 1 || near >= 4 || hq->hp < max_hq_hp)) {
    issued |= add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                                   hq->region);
  }

  std::vector<const Warrior *> defenders;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (!should_recall_for_emergency(w, M))
      continue;
    if (large_final_goal_useful(S, M, large_goal_saved(w.id)))
      continue;
    if (w.region == M.my_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.my_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    defenders.push_back(&w);
  }
  std::sort(defenders.begin(), defenders.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][M.my_hq] !=
                  P.hops[rhs->region][M.my_hq]) {
                return P.hops[lhs->region][M.my_hq] <
                       P.hops[rhs->region][M.my_hq];
              }
              return lhs->id.num < rhs->id.num;
            });

  int need_moves = std::min<int>(8, std::max(2, near + close));
  int moved = 0;
  for (const Warrior *w : defenders) {
    if (moved >= need_moves)
      break;
    int cost = move_cost_to(S, M, M.my_hq);
    if (planned_gold < cost)
      break;
    a.moves.emplace_back(w->id, M.my_hq);
    planned_gold -= cost;
    ++moved;
    issued = true;
  }
  issued |= add_front_half_hq_pressure_under_emergency(S, M, P, a,
                                                       planned_gold);

  int cap = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].train_cap;
  int want_train = close > 0 ? cap : std::min(3, cap);
  issued |= add_train_if_needed(S, M, a, planned_gold, want_train);
  return issued;
}

struct LargeBaseThreat {
  bool active = false;
  int region = -1;
  int defender_need = 0;
  int score = -1;
};

static LargeBaseThreat detect_large_base_threat(const GameState &S,
                                                const GameMap &M,
                                                const Paths &P) {
  LargeBaseThreat best;
  if (!large_strategy_active(M))
    return best;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    int enemy_here = count_enemy_warriors_at(S, b.region, M);
    int enemy_close = enemy_near_region(S, M, P, b.region, 1);
    int enemy_reachable = enemy_near_region(S, M, P, b.region, 3);
    if (enemy_here == 0 && enemy_close == 0 && enemy_reachable < 3)
      continue;
    int committed = committed_my_count_at(S, Actions{}, b.region, M);
    int need = large_base_staff_need(b) + enemy_here + enemy_close +
               enemy_reachable / 2 + (b.hp * 2 <= b.current_hp() ? 1 : 0);
    int score = enemy_here * 120 + enemy_close * 55 + enemy_reachable * 18 +
                (b.current_hp() - b.hp) * 6 - committed * 20;
    if (score > best.score) {
      best.active = true;
      best.region = b.region;
      best.defender_need = std::max(large_base_staff_need(b), need);
      best.score = score;
    }
  }
  return best;
}

static bool apply_large_base_threat_defense(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold) {
  LargeBaseThreat threat = detect_large_base_threat(S, M, P);
  if (!threat.active)
    return false;
  const Building *base = find_building(S, threat.region);
  if (base == nullptr)
    return false;

  bool issued = false;
  if (count_enemy_warriors_at(S, threat.region, M) == 0 &&
      (base->hp < base->current_hp() ||
       enemy_near_region(S, M, P, threat.region, 1) > 0)) {
    issued |= add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                                   threat.region);
  }

  int committed = committed_my_count_at(S, a, threat.region, M);
  int need_moves = std::min(6, std::max(0, threat.defender_need - committed));
  std::vector<const Warrior *> defenders;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == threat.region || warrior_already_planned(a, w.id))
      continue;
    if (is_committed_hq_assault_warrior(w, M))
      continue;
    if (P.nxt[w.region][threat.region] == -1)
      continue;
    if (P.hops[w.region][threat.region] > 3)
      continue;
    if (!can_leave_large_base_strict(S, M, a, w.region))
      continue;
    defenders.push_back(&w);
  }
  std::sort(defenders.begin(), defenders.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][threat.region] !=
                  P.hops[rhs->region][threat.region]) {
                return P.hops[lhs->region][threat.region] <
                       P.hops[rhs->region][threat.region];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  int moved = 0;
  for (const Warrior *w : defenders) {
    if (moved >= need_moves)
      break;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w,
                                      threat.region, false))
      continue;
    ++moved;
    issued = true;
  }
  return issued;
}

static bool add_large_resume_saved_goal_moves(const GameState &S,
                                              const GameMap &M,
                                              const Paths &P, Actions &a,
                                              int &planned_gold,
                                              int max_moves) {
  if (!large_strategy_active(M) || max_moves <= 0)
    return false;
  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (warrior_already_planned(a, w.id))
      continue;
    int goal = large_goal_saved(w.id);
    if (!large_final_goal_useful(S, M, goal)) {
      large_goal_clear(w.id);
      continue;
    }
    if (w.region == goal) {
      large_goal_clear(w.id);
      continue;
    }
    if (P.nxt[w.region][goal] == -1)
      continue;
    if (!can_leave_large_base_strict(S, M, a, w.region))
      continue;
    candidates.push_back(&w);
  }
  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              int lg = large_goal_saved(lhs->id);
              int rg = large_goal_saved(rhs->id);
              if (P.hops[lhs->region][lg] != P.hops[rhs->region][rg])
                return P.hops[lhs->region][lg] < P.hops[rhs->region][rg];
              return lhs->id.num < rhs->id.num;
            });

  int issued = 0;
  for (const Warrior *w : candidates) {
    if (issued >= max_moves)
      break;
    int goal = large_goal_saved(w->id);
    if (large_final_goal_useful(S, M, goal)) {
      int same_goal_candidates = 0;
      for (const Warrior *other : candidates) {
        if (large_goal_saved(other->id) == goal)
          ++same_goal_candidates;
      }
      if (!large_early_attack_gate_satisfied(S, M, a, goal,
                                             same_goal_candidates,
                                             planned_gold))
        continue;
    }
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, goal))
      continue;
    ++issued;
  }
  return issued > 0;
}

static bool add_large_idle_surplus_redeploy(const GameState &S,
                                            const GameMap &M,
                                            const Paths &P, Actions &a,
                                            int &planned_gold,
                                            int &capture_target,
                                            int max_moves,
                                            bool foundation_ready) {
  if (!large_strategy_active(M) || max_moves <= 0)
    return false;
  capture_target = select_forward_capture_target(S, M, P, capture_target);
  if (!large_final_goal_useful(S, M, capture_target))
    return false;

  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (warrior_already_planned(a, w.id) || w.region == capture_target)
      continue;
    const Building *src = find_building(S, w.region);
    if (src == nullptr || src->side != M.my_side || src->type != BType::BASE)
      continue;
    if (count_enemy_warriors_at(S, w.region, M) > 0)
      continue;
    if (enemy_near_region(S, M, P, w.region, 1) > 0)
      continue;
    int after_departures =
        count_my_stationary_at(S, w.region, M) -
        planned_moves_from_region(a, S, w.region);
    if (after_departures <= large_base_staff_need(*src))
      continue;
    if (P.nxt[w.region][capture_target] == -1)
      continue;
    if (would_pull_forward_pressure_back(M, P, w.region, capture_target))
      continue;
    candidates.push_back(&w);
  }
  std::sort(candidates.begin(), candidates.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][capture_target] !=
                  P.hops[rhs->region][capture_target]) {
                return P.hops[lhs->region][capture_target] <
                       P.hops[rhs->region][capture_target];
              }
              return lhs->id.num < rhs->id.num;
            });

  if (!foundation_ready &&
      !large_early_attack_gate_satisfied(
          S, M, a, capture_target, static_cast<int>(candidates.size()),
          planned_gold))
    return false;

  int issued = 0;
  for (const Warrior *w : candidates) {
    if (issued >= max_moves)
      break;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w,
                                      capture_target))
      continue;
    ++issued;
  }
  return issued > 0;
}

static int large_capture_desired_count(const GameState &S, const GameMap &M,
                                       const Paths &P, int target, int turn) {
  int desired = capture_attack_need(S, M, P, target);
  if (turn >= 130)
    desired += 2;
  if (turn >= 150)
    desired += 4;
  if (turn >= 175)
    desired += 4;
  return std::min(24, std::max(8, desired));
}

static int large_capture_committed_count(const GameState &S, const GameMap &M,
                                         const Actions &a, int target) {
  int committed = committed_my_count_at(S, a, target, M);
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    if (w.state == WState::MOVING && large_goal_saved(w.id) == target)
      ++committed;
  }
  return committed;
}

static int select_large_hq_surplus_capture_target(
    const GameState &S, const GameMap &M, const Paths &P, const Actions &a,
    int current_target, int turn) {
  auto usable = [&](int region) {
    const Building *b = find_building(S, region);
    return b != nullptr && b->side != M.my_side && b->type == BType::BASE &&
           P.nxt[M.my_hq][region] != -1 &&
           large_capture_committed_count(S, M, a, region) <
               large_capture_desired_count(S, M, P, region, turn);
  };

  (void)current_target;

  int best = -1;
  double best_score = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side || b.type != BType::BASE)
      continue;
    if (!usable(b.region))
      continue;
    double score = center_first_enemy_base_score(S, M, P, b);
    if (score < best_score) {
      best_score = score;
      best = b.region;
    }
  }
  return best;
}

static bool large_hq_surplus_capture_allowed(const GameState &S,
                                             const GameMap &M,
                                             const Paths &P,
                                             const Actions &a, int turn,
                                             bool foundation_ready) {
  if (!large_strategy_active(M))
    return false;
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr)
    return false;
  if (count_enemy_warriors_at(S, M.my_hq, M) > 0)
    return false;
  int hq_ready = count_my_stationary_at(S, M.my_hq, M) -
                 planned_moves_from_region(a, S, M.my_hq);
  if (turn >= 70 && hq_ready >= 9)
    return true;
  if (foundation_ready)
    return true;
  if (hq->level < 4 || turn < 125)
    return false;
  int goal = active_macro_target_goal(S, M, P);
  int built = count_target_bases_built(S, M, P);
  int level2 = count_target_level2_bases(S, M, P);
  if (built < std::min(6, goal) || level2 < std::min(4, goal))
    return false;
  return large_base_level_staff_deficit(S, a, M) <= 8;
}

static bool add_large_hq_surplus_capture_push(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int turn, int &capture_target,
    std::set<int> &capture_regions, int max_moves,
    bool force_worker_reserve = false) {
  if (!large_strategy_active(M) || max_moves <= 0)
    return false;
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr)
    return false;
  if (count_enemy_warriors_at(S, M.my_hq, M) > 0)
    return false;

  int hq_ready = count_my_stationary_at(S, M.my_hq, M) -
                 planned_moves_from_region(a, S, M.my_hq);
  bool hq_overflow = turn >= 70 && hq_ready >= 9;
  bool forward_support =
      force_worker_reserve && turn >= 70 && hq_ready > std::max(1, hq->level);
  hq_overflow = hq_overflow || forward_support;
  if (!hq_overflow && hq->level < 4)
    return false;

  capture_target =
      select_large_hq_surplus_capture_target(S, M, P, a, capture_target, turn);
  const Building *target_building = find_building(S, capture_target);
  if (target_building == nullptr || target_building->side == M.my_side ||
      target_building->type != BType::BASE) {
    return false;
  }

  int hq_work_cap = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].work_cap;
  int reserve = hq_overflow ? std::max(1, hq->level) : hq_work_cap + 2;
  if (!hq_overflow && turn >= 150)
    reserve = hq_work_cap + 1;
  if (!hq_overflow && turn >= 175)
    reserve = hq_work_cap;
  int available = std::max(0, hq_ready - reserve);
  if (available <= 0)
    return false;

  int committed = large_capture_committed_count(S, M, a, capture_target);
  int desired = large_capture_desired_count(S, M, P, capture_target, turn);
  int need = std::max(0, desired - committed);
  if (need <= 0)
    return false;

  std::vector<const Warrior *> candidates;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region != M.my_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][capture_target] == -1)
      continue;
    candidates.push_back(&w);
  }
  std::sort(candidates.begin(), candidates.end(),
            [](const Warrior *lhs, const Warrior *rhs) {
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  int issued = 0;
  int issue_limit = std::min({available, need, max_moves});
  int potential_issue =
      std::min(issue_limit, static_cast<int>(candidates.size()));
  if (!large_early_attack_gate_satisfied(S, M, a, capture_target,
                                         potential_issue, planned_gold))
    return false;
  int gate_committed =
      early_large_attack_committed_count(S, M, a, capture_target);
  size_t move_mark = a.moves.size();
  int gold_mark = planned_gold;
  std::vector<std::pair<WarriorId, int>> saved_goal_mark;
  for (const Warrior *w : candidates) {
    if (issued >= issue_limit)
      break;
    hq_ready = count_my_stationary_at(S, M.my_hq, M) -
               planned_moves_from_region(a, S, M.my_hq);
    if (hq_ready <= reserve)
      break;
    int cost = move_cost_to(S, M, capture_target);
    if (planned_gold < cost)
      break;
    if (!can_leave_large_base_strict(S, M, a, w->region))
      continue;
    int old_goal = large_goal_saved(w->id);
    a.moves.emplace_back(w->id, capture_target);
    planned_gold -= cost;
    large_goal_remember(w->id, capture_target);
    saved_goal_mark.emplace_back(w->id, old_goal);
    ++issued;
  }
  if (gate_committed + issued < 3) {
    a.moves.resize(move_mark);
    planned_gold = gold_mark;
    for (const auto &entry : saved_goal_mark) {
      if (entry.second >= 0)
        large_goal_remember(entry.first, entry.second);
      else
        large_goal_clear(entry.first);
    }
    return false;
  }
  if (issued <= 0)
    return false;
  capture_regions.insert(capture_target);
  add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                            capture_target);
  return true;
}

static bool apply_sub90_warm_hq_defense(const GameState &S, const GameMap &M,
                                        const Paths &P, Actions &a,
                                        std::set<int> &used_upgrades,
                                        int &planned_gold,
                                        const Building *hq) {
  if (hq == nullptr)
    return false;

  int close = enemy_near_region(S, M, P, M.my_hq, 1);
  int near = enemy_near_region(S, M, P, M.my_hq, 2);
  if (close == 0 && near < 4)
    return false;
  if (!hq_assault_urgent_threat_active(S, M, P))
    return false;

  bool issued = false;
  int max_hq_hp = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].hp;
  bool can_upgrade_hq_for_defense = hq->level < 3;
  if (can_upgrade_hq_for_defense &&
      (close >= 1 || near >= 4 || hq->hp < max_hq_hp)) {
    issued |= add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                                   hq->region);
  }

  std::vector<const Warrior *> defenders;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.my_hq || warrior_already_planned(a, w.id))
      continue;
    if (is_committed_hq_assault_warrior(w, M))
      continue;
    if (P.nxt[w.region][M.my_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    defenders.push_back(&w);
  }
  std::sort(defenders.begin(), defenders.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][M.my_hq] !=
                  P.hops[rhs->region][M.my_hq]) {
                return P.hops[lhs->region][M.my_hq] <
                       P.hops[rhs->region][M.my_hq];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  int need_moves = std::min<int>(10, std::max(2, near + close));
  int moved = 0;
  for (const Warrior *w : defenders) {
    if (moved >= need_moves)
      break;
    int cost = move_cost_to(S, M, M.my_hq);
    if (planned_gold < cost)
      break;
    a.moves.emplace_back(w->id, M.my_hq);
    planned_gold -= cost;
    ++moved;
    issued = true;
  }

  int cap = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].train_cap;
  issued |= add_train_if_needed(S, M, a, planned_gold, cap);
  return issued;
}

[[maybe_unused]] static bool add_all_in_moves(const GameState &S,
                                              const GameMap &M, const Paths &P,
                                              Actions &a, int &planned_gold) {
  std::vector<const Warrior *> attackers;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (!can_move_non_emergency(S, M, a, w))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    attackers.push_back(&w);
  }

  std::sort(attackers.begin(), attackers.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.dist[lhs->region][M.opp_hq] !=
                  P.dist[rhs->region][M.opp_hq]) {
                return P.dist[lhs->region][M.opp_hq] <
                       P.dist[rhs->region][M.opp_hq];
              }
              return lhs->id.num < rhs->id.num;
            });

  bool issued = false;
  for (const Warrior *w : attackers) {
    int cost = move_cost_to(S, M, M.opp_hq);
    if (planned_gold < cost)
      break;
    a.moves.emplace_back(w->id, M.opp_hq);
    planned_gold -= cost;
    issued = true;
  }
  return issued;
}

[[maybe_unused]] static bool add_pre_hq5_train_if_needed(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold) {
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr || hq->level >= HQ_MAX_LEVEL)
    return false;
  if (a.train_n > 0 || planned_gold < TRAIN_COST)
    return false;

  int target = next_unbuilt_target(S, M, P);
  bool need_worker = false;
  if (target != -1) {
    if (count_my_warriors_at(S, target, M) > 0 &&
        count_enemy_warriors_at(S, target, M) == 0) {
      return false;
    }
    if (has_worker_heading_to(S, M, target))
      return false;
    need_worker = true;
  }
  const Building *level1 = next_level1_target_base(S, M, P);
  if (level1 != nullptr && count_my_warriors_at(S, level1->region, M) == 0)
    need_worker = true;

  int min_workers = 1 + count_my_bases(S, M);
  if (count_my_alive(S, M) <= min_workers)
    need_worker = true;

  if (!need_worker)
    return false;
  return add_train_if_needed(S, M, a, planned_gold, 1);
}

static bool target_macro_complete_large(const GameState &S, const Actions &a,
                                        const GameMap &M, const Paths &P) {
  const Building *hq = my_hq_building(S, M);
  int goal = active_macro_target_goal(S, M, P);
  return hq != nullptr && hq->level >= HQ_MAX_LEVEL &&
         count_target_bases_built(S, M, P) >= goal &&
         count_target_level2_bases(S, M, P) >= goal &&
         target_base_worker_deficit(S, a, M, P) == 0;
}

static bool large_foundation_ready_for_attack(const GameState &S,
                                              const Actions &a,
                                              const GameMap &M,
                                              const Paths &P) {
  (void)a;
  if (!large_strategy_active(M))
    return true;
  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr || hq->level < HQ_MAX_LEVEL)
    return false;
  int goal = active_macro_target_goal(S, M, P);
  int built = count_target_bases_built(S, M, P);
  int level2 = count_target_level2_bases(S, M, P);
  int built_goal = std::min(goal, 6);
  int core_level2 = std::min(goal, 4);
  return built >= built_goal && level2 >= core_level2;
}

static bool large_foundation_hq_upgrade_allowed(const GameState &S,
                                                const GameMap &M,
                                                const Paths &P, int turn,
                                                const Building *hq) {
  if (!large_strategy_active(M) || hq == nullptr || hq->level >= HQ_MAX_LEVEL)
    return false;
  if (count_enemy_warriors_at(S, M.my_hq, M) > 0)
    return false;

  int goal = active_macro_target_goal(S, M, P);
  int built = count_target_bases_built(S, M, P);
  int level2 = count_target_level2_bases(S, M, P);
  int next_level = hq->level + 1;
  if (next_level == 2)
    return built >= std::min(6, goal);
  if (next_level == 3)
    return built >= std::min(6, goal) &&
           (level2 >= std::min(4, goal) || turn >= 82);
  if (next_level == 4)
    return built >= std::min(6, goal) &&
           (level2 >= std::min(4, goal) || turn >= 105);
  if (next_level == 5)
    return built >= std::min(6, goal) &&
           (level2 >= std::min(4, goal) || turn >= 120);
  return false;
}

static bool add_large_foundation_hq_upgrade_if_ready(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, int turn,
    const Building *hq) {
  if (!large_foundation_hq_upgrade_allowed(S, M, P, turn, hq))
    return false;
  if (used_upgrades.count(hq->region))
    return false;
  int cost = HQ_LEVELS[hq->level + 1].upgrade_cost;
  if (planned_gold < cost)
    return false;
  return add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                              hq->region);
}

static void clear_large_enemy_saved_goals_before_foundation(
    const GameState &S, const GameMap &M) {
  if (!large_strategy_active(M) || g_large_saved_goal_by_warrior.empty())
    return;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    int goal = large_goal_saved(w.id);
    if (goal == M.opp_hq) {
      large_goal_clear(w.id);
    }
  }
}
static Actions decide_large_recovery(const GameState &S, const GameMap &M, const Paths &P,
                      int turn) {
  Actions a;
  std::set<int> used_upgrades;
  int planned_gold = std::max(0, S.gold);

  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr)
    return a;

  static int forward_capture_target = -1;
  static std::set<int> forward_capture_regions;
  static int max_my_bases_seen = 0;
  static std::set<int> ever_owned_base_regions;
  static int low_base_recovery_target = -1;
  if (turn <= 1) {
    forward_capture_target = -1;
    forward_capture_regions.clear();
    max_my_bases_seen = 0;
    ever_owned_base_regions.clear();
    low_base_recovery_target = -1;
    large_goal_memory_reset();
  }

  int current_my_bases = count_my_bases(S, M);
  max_my_bases_seen = std::max(max_my_bases_seen, current_my_bases);
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side && b.type == BType::BASE)
      ever_owned_base_regions.insert(b.region);
  }

  int planned_bases = current_my_bases;
  int target_bases = count_target_bases_built(S, M, P);
  std::vector<int> targets = log2_target_order(S, M, P);
  int active_target_goal =
      std::min(TARGET_BASE_COUNT, static_cast<int>(targets.size()));
  int hq2_base_gate = std::min(6, active_target_goal);
  int hq3_level2_gate = std::min(5, active_target_goal);
  int hq4_level2_gate = std::min(9, active_target_goal);
  int hq5_level2_gate = active_target_goal;
  int preupgrade_target = next_level1_upgrade_target_region(S, M, P);
  bool foundation_ready =
      large_foundation_ready_for_attack(S, a, M, P);
  if (!foundation_ready)
    clear_large_enemy_saved_goals_before_foundation(S, M);

  bool enemy_inside_hq = count_enemy_warriors_at(S, M.my_hq, M) > 0;
  if (enemy_inside_hq) {
    add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
    for (const auto &w : S.warriors) {
      if (w.id.side != M.my_side || w.state != WState::STATIONARY)
        continue;
      if (!should_recall_for_emergency(w, M))
        continue;
      if (w.region == M.my_hq || warrior_already_planned(a, w.id))
        continue;
      if (P.nxt[w.region][M.my_hq] == -1)
        continue;
      int cost = move_cost_to(S, M, M.my_hq);
      if (planned_gold < cost)
        break;
      a.moves.emplace_back(w.id, M.my_hq);
      planned_gold -= cost;
    }
    add_front_half_hq_pressure_under_emergency(S, M, P, a, planned_gold);
    add_train_if_needed(S, M, a, planned_gold, hq->level < 5 ? 1 : 3);
    return a;
  }

  bool issued_hq_approach_defense =
      apply_large_map_hq_approach_defense(S, M, P, a, used_upgrades,
                                          planned_gold, hq);
  if (issued_hq_approach_defense && !foundation_ready) {
    return a;
  }

  if (M.N <= 56 && turn >= 70 && total_worker_deficit(S, a, M) > 0 &&
      add_worker_fill_moves(S, M, P, a, planned_gold)) {
    return a;
  }

  add_forward_base_builds(S, M, a, used_upgrades, planned_gold, planned_bases,
                          forward_capture_regions);
  if (!a.upgrades.empty()) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }
  if (captured_base_build_waiting(S, M, used_upgrades,
                                  forward_capture_regions)) {
    return a;
  }

  bool forward_chain_active =
      !forward_capture_regions.empty() || count_forward_my_bases(S, M, P) > 0;
  if (large_hq_surplus_capture_allowed(S, M, P, a, turn,
                                       foundation_ready) ||
      (M.N >= 90 && turn >= 70 && forward_chain_active)) {
    int hq_push_limit = turn >= 150 ? 16 : 12;
    if (add_large_hq_surplus_capture_push(S, M, P, a, planned_gold, turn,
                                          forward_capture_target,
                                          forward_capture_regions,
                                          hq_push_limit,
                                          forward_chain_active)) {
      int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
      if (a.train_n == 0)
        add_train_if_needed(S, M, a, planned_gold,
                            affordable_train_count(planned_gold, cap));
      return a;
    }
  }

  if (add_large_foundation_hq_upgrade_if_ready(
          S, M, P, a, used_upgrades, planned_gold, turn, hq)) {
    int cap = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].train_cap;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (turn >= 35 && minimum_staff_deficit(S, a, M) > 0 &&
      add_critical_worker_fill_moves(S, M, P, a, planned_gold)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (M.N >= 90 && !foundation_ready && turn >= 35 &&
      large_base_level_staff_deficit(S, a, M) > 0) {
    bool issued_staff = false;
    issued_staff |= add_target_base_fill_moves(S, M, P, a, planned_gold, 6,
                                               preupgrade_target);
    issued_staff |= add_captured_base_fill_moves(S, M, P, a, planned_gold,
                                                 forward_capture_regions);
    if (!issued_staff)
      issued_staff |= add_worker_fill_moves(S, M, P, a, planned_gold);
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    if (issued_staff || a.train_n > 0)
      return a;
  }

  if (large_hq_surplus_capture_allowed(S, M, P, a, turn,
                                       foundation_ready) ||
      (M.N >= 90 && turn >= 70 && forward_chain_active)) {
    int hq_push_limit = turn >= 175 ? 14 : (turn >= 150 ? 12 : 8);
    add_large_hq_surplus_capture_push(S, M, P, a, planned_gold, turn,
                                      forward_capture_target,
                                      forward_capture_regions,
                                      hq_push_limit,
                                      forward_chain_active);
  }

  if (apply_large_base_threat_defense(S, M, P, a, used_upgrades,
                                      planned_gold)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (add_large_limited_macro_recovery(
          S, M, P, a, used_upgrades, planned_gold, planned_bases,
          max_my_bases_seen, ever_owned_base_regions, low_base_recovery_target,
          hq)) {
    return a;
  }

  if (!foundation_ready && turn >= 150 && total_worker_deficit(S, a, M) > 0 &&
      add_worker_fill_moves(S, M, P, a, planned_gold)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (foundation_ready) {
    add_large_resume_saved_goal_moves(S, M, P, a, planned_gold, 12);
    add_large_idle_surplus_redeploy(S, M, P, a, planned_gold,
                                    forward_capture_target, 8,
                                    foundation_ready);
  }

  if (add_hq_upgrade_when_enemy_bases_low(S, M, P, a, used_upgrades,
                                          planned_gold, turn, hq)) {
    int cap = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].train_cap;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (foundation_ready &&
      add_low_enemy_base_hq_pressure(S, M, P, a, planned_gold, turn)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (foundation_ready &&
      add_late_direct_hq_pressure(S, M, P, a, planned_gold, turn)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (foundation_ready && add_late_split_capture_if_favorable(
          S, M, P, a, planned_gold, turn, forward_capture_target,
          forward_capture_regions)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (foundation_ready &&
      add_large_distributed_hq_pressure_if_ready(S, M, P, a, planned_gold,
                                                 turn)) {
    return a;
  }

  if (foundation_ready && hq->level >= HQ_MAX_LEVEL && turn >= 140 && current_my_bases >= 4 &&
      !hq_assault_urgent_threat_active(S, M, P) &&
      large_hq_pressure_feasible(S, M, P, a, turn) &&
      add_staged_hq_assault_moves(S, M, P, a, planned_gold, turn)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (foundation_ready && (hq->level >= HQ_MAX_LEVEL || turn >= 105) &&
      add_decisive_hq_push_if_ready(S, M, P, a, planned_gold, turn))
    return a;

  if (foundation_ready && add_late_total_all_in_moves(S, M, P, a, planned_gold, turn))
    return a;

  add_captured_base_fill_moves(S, M, P, a, planned_gold,
                               forward_capture_regions);
  int capture_staff_deficit =
      captured_base_worker_deficit(S, M, a, forward_capture_regions);

  if (hq->level < HQ_MAX_LEVEL && !used_upgrades.count(hq->region)) {
    int next_level = hq->level + 1;
    int target_level2 = count_target_level2_bases(S, M, P);
    bool allow_hq = false;
    if (M.N >= 90) {
      allow_hq = large_foundation_hq_upgrade_allowed(S, M, P, turn, hq);
    } else if (next_level == 2) {
      allow_hq = target_bases >= hq2_base_gate;
    } else if (next_level == 3) {
      allow_hq = target_level2 >= hq3_level2_gate || turn >= 89 ||
                 allow_favorable_hq3_pressure(S, M, P, a, planned_gold, turn,
                                              current_my_bases);
    } else if (next_level == 4) {
      allow_hq = target_level2 >= hq4_level2_gate || turn >= 127;
    } else if (next_level == 5) {
      allow_hq = target_level2 >= hq5_level2_gate ||
                 (target_level2 >= core_level2_goal(active_target_goal) &&
                  count_forward_my_bases(S, M, P) > 0) ||
                 turn >= 140;
    }
    if (M.N < 90 && next_level >= 4)
      allow_hq = false;
    if (allow_hq &&
        !add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                              hq->region)) {
      add_target_base_fill_moves(S, M, P, a, planned_gold, 4,
                                 preupgrade_target);
      return a;
    }
  }

  for (int target : targets) {
    if (planned_bases >= TARGET_BASE_COUNT)
      break;
    if (enemy_building_at(S, M, target) || is_my_base_at(S, M, target))
      continue;
    if (count_my_warriors_at(S, target, M) == 0 ||
        count_enemy_warriors_at(S, target, M) > 0) {
      continue;
    }
    add_base_build(S, M, a, used_upgrades, planned_gold, planned_bases,
                   target);
  }

  int target_level2 = count_target_level2_bases(S, M, P);
  if (hq->level < HQ_MAX_LEVEL && !used_upgrades.count(hq->region)) {
    int next_level = hq->level + 1;
    bool allow_hq = false;
    if (M.N >= 90) {
      allow_hq = large_foundation_hq_upgrade_allowed(S, M, P, turn, hq);
    } else if (next_level == 2) {
      allow_hq = target_bases >= hq2_base_gate;
    } else if (next_level == 3) {
      allow_hq = target_level2 >= hq3_level2_gate || turn >= 89 ||
                 allow_favorable_hq3_pressure(S, M, P, a, planned_gold, turn,
                                              current_my_bases);
    } else if (next_level == 4) {
      allow_hq = target_level2 >= hq4_level2_gate || turn >= 127;
    } else if (next_level == 5) {
      allow_hq = target_level2 >= hq5_level2_gate ||
                 (target_level2 >= core_level2_goal(active_target_goal) &&
                  count_forward_my_bases(S, M, P) > 0) ||
                 turn >= 140;
    }
    if (M.N < 90 && next_level >= 4)
      allow_hq = false;
    if (allow_hq)
      add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
  }

  foundation_ready = large_foundation_ready_for_attack(S, a, M, P);
  bool capture_phase_ready =
      foundation_ready && hq->level >= 2 &&
      (!has_open_neutral_target(S, M, P) || target_bases >= active_target_goal ||
       turn >= 95) &&
      (target_level2 >= core_level2_goal(active_target_goal) || turn >= 85);
  int capture_need_for_training = 0;
  if (capture_phase_ready && capture_staff_deficit == 0) {
    forward_capture_target =
        select_forward_capture_target(S, M, P, forward_capture_target);
    if (forward_capture_target != -1) {
      forward_capture_regions.insert(forward_capture_target);
      int need = capture_attack_need(S, M, P, forward_capture_target);
      capture_need_for_training = need;
      add_forward_capture_moves(S, M, P, a, planned_gold,
                                forward_capture_target, need,
                                forward_capture_regions);
    }
  }

  for (int target : targets) {
    const Building *b = find_building(S, target);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE ||
        b->level >= 2) {
      continue;
    }
    if (build_phase_stationary_count_at(S, a, target, M) < 2)
      continue;
    add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, target);
  }

  int planned_target_level2 = target_level2;
  for (int region : a.upgrades) {
    const Building *b = find_building(S, region);
    if (b != nullptr && b->side == M.my_side && b->type == BType::BASE &&
        b->level == 1) {
      ++planned_target_level2;
    }
  }

  if (hq->level < HQ_MAX_LEVEL && !used_upgrades.count(hq->region)) {
    int next_level = hq->level + 1;
    bool allow_hq = false;
    if (M.N >= 90) {
      allow_hq = large_foundation_hq_upgrade_allowed(S, M, P, turn, hq);
    } else if (next_level == 2) {
      allow_hq = target_bases >= hq2_base_gate;
    } else if (next_level == 3) {
      allow_hq = planned_target_level2 >= hq3_level2_gate || turn >= 89 ||
                 allow_favorable_hq3_pressure(S, M, P, a, planned_gold, turn,
                                              current_my_bases);
    } else if (next_level == 4) {
      allow_hq = planned_target_level2 >= hq4_level2_gate || turn >= 127;
    } else if (next_level == 5) {
      allow_hq = planned_target_level2 >= hq5_level2_gate ||
                 (planned_target_level2 >= core_level2_goal(active_target_goal) &&
                  count_forward_my_bases(S, M, P) > 0) ||
                 turn >= 140;
    }
    if (M.N < 90 && next_level >= 4)
      allow_hq = false;
    if (allow_hq)
      add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
  }

  bool macro_complete = target_macro_complete_large(S, a, M, P);
  if (!macro_complete) {
    add_target_base_fill_moves(S, M, P, a, planned_gold, 4,
                               preupgrade_target);

    int issued_workers = 0;
    for (int target : targets) {
      if (issued_workers >= 3)
        break;
      if (enemy_building_at(S, M, target) || is_my_base_at(S, M, target))
        continue;
      if (has_worker_or_pending_for_target(S, M, target))
        continue;
      if (add_worker_move_to_target(S, M, P, a, planned_gold, target, true,
                                    preupgrade_target, 2))
        ++issued_workers;
    }

    if (M.N >= 90) {
      add_large_idle_surplus_redeploy(S, M, P, a, planned_gold,
                                      forward_capture_target, 8,
                                      foundation_ready);
    } else {
      add_excess_base_moves_to_hq(S, M, P, a, planned_gold, 4,
                                  preupgrade_target, 2);
    }

    int desired_alive = 1 + active_target_goal * 2 + hq->work_cap();
    desired_alive += capture_need_for_training;
    desired_alive += capture_staff_deficit;
    if (hq->level >= HQ_MAX_LEVEL)
      desired_alive += 12;
    int train_cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    int current_after_train = count_my_alive(S, M) + a.train_n;
    int want_train = std::max(0, desired_alive - current_after_train);

    bool build_waiting = false;
    for (int target : targets) {
      if (!is_my_base_at(S, M, target) && !enemy_building_at(S, M, target) &&
          count_my_warriors_at(S, target, M) > 0 &&
          count_enemy_warriors_at(S, target, M) == 0) {
        build_waiting = true;
      }
    }

    int reserve_gold = 0;
    if (build_waiting)
      reserve_gold += BASE_LEVELS[1].cost;
    int pending_build_sites = 0;
    for (int target : targets) {
      if (used_upgrades.count(target))
        continue;
      if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
        continue;
      bool pending_worker = has_worker_heading_to(S, M, target) ||
                            planned_moves_to_region(a, target) > 0 ||
                            count_my_warriors_at(S, target, M) > 0;
      if (pending_worker)
        ++pending_build_sites;
    }
    reserve_gold += BASE_LEVELS[1].cost * pending_build_sites;
    if (count_target_bases_built(S, M, P) >= active_target_goal &&
        count_target_level2_bases(S, M, P) < active_target_goal) {
      reserve_gold += BASE_LEVELS[2].cost;
    }

    int train_gold = std::max(0, planned_gold - reserve_gold);
    if (want_train > 0 && train_gold >= TRAIN_COST) {
      int train_plan_gold = train_gold;
      add_train_if_needed(S, M, a, train_plan_gold,
                          std::min(train_cap, want_train));
      if (a.train_n > 0)
        planned_gold -= a.train_n * TRAIN_COST;
    }

    if (a.train_n == 0 && hq->level >= HQ_MAX_LEVEL &&
        train_gold >= TRAIN_COST) {
      int train_plan_gold = train_gold;
      add_train_if_needed(S, M, a, train_plan_gold,
                          affordable_train_count(
                              train_gold, HQ_LEVELS[hq->level].train_cap));
      if (a.train_n > 0)
        planned_gold -= a.train_n * TRAIN_COST;
    }
    add_optional_rebuild_lost_bases(S, M, a, used_upgrades, planned_gold,
                                    planned_bases, ever_owned_base_regions);
    return a;
  }

  for (int target : targets) {
    const Building *b = find_building(S, target);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE ||
        b->level != 1) {
      continue;
    }
    if (build_phase_stationary_count_at(S, a, target, M) < 2)
      continue;
    if (add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, target))
      return a;
  }

  for (int target : targets) {
    const Building *b = find_building(S, target);
    if (b == nullptr || b->side != M.my_side || b->type != BType::BASE ||
        b->level != 1) {
      continue;
    }
    if (committed_my_count_at(S, a, target, M) >= 2)
      continue;
    if (add_surplus_moves_to_region(S, M, P, a, planned_gold, target, 1))
      return a;
  }

  const Building *rally = my_hq_building(S, M);
  if (add_rally_attack_if_ready(S, M, P, a, planned_gold, rally))
    return a;

  add_worker_fill_moves(S, M, P, a, planned_gold);
  add_rally_gather_moves(S, M, P, a, planned_gold, rally);

  int cap = HQ_LEVELS[hq->level].train_cap;
  int wanted = std::max(total_worker_deficit(S, a, M),
                        RALLY_ATTACK_COUNT -
                            (rally == nullptr
                                 ? 0
                                 : effective_my_count_at(S, a,
                                                         rally->region, M)));
  add_train_if_needed(S, M, a, planned_gold,
                      std::min(cap, std::max(0, wanted)));
  if (a.train_n == 0) {
    add_train_if_needed(S, M, a, planned_gold,
                        affordable_train_count(planned_gold, cap));
  }
  add_optional_rebuild_lost_bases(S, M, a, used_upgrades, planned_gold,
                                  planned_bases, ever_owned_base_regions);
  return a;
}

static std::vector<int> sub90_warm_initial_targets(const GameState &S,
                                                   const GameMap &M,
                                                   const Paths &P) {
  if (M.N >= 71) {
    std::vector<int> out;
    std::set<int> used;
    auto add_wanted = [&](int wanted, bool own_side_required) {
      int best = -1;
      double best_score = std::numeric_limits<double>::infinity();
      for (int r : M.strongholds) {
        if (used.count(r))
          continue;
        const Building *b = find_building(S, r);
        if (b != nullptr && b->side != M.my_side)
          continue;
        if (P.nxt[M.my_hq][r] == -1)
          continue;
        if (own_side_required && !is_own_side_region(M, P, r))
          continue;
        double score = std::abs(r - wanted) * 100.0 + P.dist[M.my_hq][r] * 0.01 +
                       enemy_near_region(S, M, P, r, 2) * 300.0;
        if (score < best_score) {
          best_score = score;
          best = r;
        }
      }
      if (best != -1) {
        out.push_back(best);
        used.insert(best);
      }
    };
    const std::vector<int> left_order = {7, 36, 1, 22, 14, 25, 30};
    for (int wanted_left : left_order) {
      int wanted = M.my_side == Side::LEFT ? wanted_left : M.N - 1 - wanted_left;
      bool own_side_required = wanted_left != 36;
      add_wanted(wanted, own_side_required);
    }
    return out;
  }

  struct Candidate {
    int region;
    double score;
  };
  std::vector<Candidate> candidates;
  for (int r : M.strongholds) {
    const Building *b = find_building(S, r);
    if (b != nullptr && b->side != M.my_side)
      continue;
    if (count_enemy_warriors_at(S, r, M) > 0)
      continue;
    if (P.nxt[M.my_hq][r] == -1)
      continue;
    bool own_side = is_own_side_region(M, P, r);
    if (!own_side && count_my_bases(S, M) < 1)
      continue;
    double center = std::abs(r - M.N / 2);
    double score = P.hops[M.my_hq][r] * 18.0 + P.dist[M.my_hq][r] * 0.01 +
                   enemy_near_region(S, M, P, r, 2) * 300.0;
    if (own_side)
      score -= 120.0;
    if (M.N >= 71 && count_my_bases(S, M) >= 1)
      score -= (M.N / 2.0 - std::min<double>(center, M.N / 2.0)) * 4.0;
    candidates.push_back(Candidate{r, score});
  }
  std::sort(candidates.begin(), candidates.end(),
            [](const Candidate &lhs, const Candidate &rhs) {
              if (lhs.score != rhs.score)
                return lhs.score < rhs.score;
              return lhs.region < rhs.region;
            });
  std::vector<int> out;
  int limit = M.N >= 71 ? 7 : 6;
  for (const Candidate &c : candidates) {
    if (static_cast<int>(out.size()) >= limit)
      break;
    out.push_back(c.region);
  }
  return out;
}

static int sub90_warm_base_goal(const GameMap &M) {
  return M.N >= 71 ? 7 : 6;
}

static int nearest_my_building_hops_any(const GameState &S, const GameMap &M,
                                        const Paths &P, int region) {
  int best = M.N + 1;
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side)
      best = std::min(best, P.hops[b.region][region]);
  }
  return best;
}

static int select_warm_capture_target(const GameState &S, const GameMap &M,
                                      const Paths &P, int current_target,
                                      int turn) {
  auto usable = [&](int region) {
    const Building *b = find_building(S, region);
    return b != nullptr && b->side != M.my_side && b->type == BType::BASE &&
           P.nxt[M.my_hq][region] != -1;
  };
  auto forward_target = [&](int region) {
    return is_front_half_region_for_my_side(M, region);
  };
  if (current_target >= 0 && usable(current_target)) {
    bool allow_stick = true;
    if (M.N < 71 && turn >= 90) {
      int left_route_a = 54;
      int left_route_b = 58;
      int route_a = M.my_side == Side::LEFT ? left_route_a : M.N - 1 - left_route_a;
      int route_b = M.my_side == Side::LEFT ? left_route_b : M.N - 1 - left_route_b;
      allow_stick = current_target == route_a || current_target == route_b;
    }
    if (allow_stick &&
        (turn < 80 || forward_target(current_target) ||
         count_enemy_bases(S, M) <= 3)) {
      return current_target;
    }
  }

  if (M.N < 71 && turn >= 90) {
    const int small_left_order[] = {54, 58, 51, 48, 32, 31, 30, 14, 11, 8};
    for (int wanted_left : small_left_order) {
      int wanted = M.my_side == Side::LEFT ? wanted_left : M.N - 1 - wanted_left;
      if (wanted >= 0 && wanted < M.N && usable(wanted))
        return wanted;
    }
  }

  if (current_target >= 0 && usable(current_target)) {
    if (turn < 80 || forward_target(current_target) ||
        count_enemy_bases(S, M) <= 3) {
      return current_target;
    }
  }

  if (M.N >= 71 && turn >= 80) {
    const int warm_left_order[] = {50, 58, 42, 65, 47, 71, 22, 14, 25};
    for (int wanted_left : warm_left_order) {
      int wanted = M.my_side == Side::LEFT ? wanted_left : M.N - 1 - wanted_left;
      if (wanted >= 0 && wanted < M.N && usable(wanted))
        return wanted;
    }
  }

  int best = -1;
  double best_score = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side || b.type != BType::BASE)
      continue;
    if (P.nxt[M.my_hq][b.region] == -1)
      continue;
    int nearest = nearest_my_building_hops_any(S, M, P, b.region);
    if (nearest > M.N)
      continue;
    int enemy_here = count_enemy_warriors_at(S, b.region, M);
    int enemy_near = enemy_near_region(S, M, P, b.region, 1);
    bool forward = forward_target(b.region);
    double forward_bonus = forward ? (turn >= 80 ? 650.0 : 320.0) : 0.0;
    double back_penalty =
        (turn >= 80 && !is_front_half_region_for_my_side(M, b.region)) ? 320.0
                                                                       : 0.0;
    double score = nearest * 45.0 + P.hops[M.my_hq][b.region] * 2.0 +
                   b.level * 55.0 + b.hp * 4.0 + enemy_here * 90.0 +
                   enemy_near * 35.0 + back_penalty - forward_bonus;
    if (score < best_score) {
      best_score = score;
      best = b.region;
    }
  }
  return best;
}

static int warm_capture_attack_need(const GameState &S, const GameMap &M,
                                    const Paths &P, int target, int turn) {
  const Building *b = find_building(S, target);
  if (b == nullptr || b->side == M.my_side || b->type != BType::BASE)
    return 0;
  int enemy_here = count_enemy_warriors_at(S, target, M);
  int enemy_support = std::max(0, enemy_near_region(S, M, P, target, 1) -
                                      enemy_here);
  int need = 4 + enemy_here;
  need += std::max(0, b->level - 1) * 2;
  need += std::max(0, b->hp - BASE_LEVELS[1].hp + 5) / 6;
  need += enemy_support / 2;
  if (turn >= 120)
    need += 1;
  return std::min(20, std::max(5, need));
}

static bool sub90_waiting_initial_build(const GameState &S, const GameMap &M,
                                        const std::vector<int> &targets,
                                        int planned_bases) {
  if (planned_bases >= sub90_warm_base_goal(M))
    return false;
  for (int target : targets) {
    if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
      continue;
    if (has_target_worker_or_pending(S, M, target) &&
        count_enemy_warriors_at(S, target, M) == 0) {
      return true;
    }
  }
  return false;
}

static std::vector<int> sub90_early_raid_opening_targets(
    const GameState &S, const GameMap &M, const Paths &P) {
  struct Candidate {
    int region;
    double direct;
    int hops;
    double dist;
    int enemy_near;
    int side_tie;
  };
  std::vector<Candidate> candidates;
  for (int r : M.strongholds) {
    const Building *b = find_building(S, r);
    if (b != nullptr && b->side != M.my_side)
      continue;
    if (count_enemy_warriors_at(S, r, M) > 0)
      continue;
    if (P.nxt[M.my_hq][r] == -1)
      continue;
    int side_tie = M.my_side == Side::LEFT ? r : -r;
    candidates.push_back(Candidate{
        r, euclid_ceil(M, M.my_hq, r), P.hops[M.my_hq][r], P.dist[M.my_hq][r],
        enemy_near_region(S, M, P, r, 2), side_tie});
  }
  std::sort(candidates.begin(), candidates.end(),
            [](const Candidate &lhs, const Candidate &rhs) {
              if (lhs.direct != rhs.direct)
                return lhs.direct < rhs.direct;
              if (lhs.hops != rhs.hops)
                return lhs.hops < rhs.hops;
              if (lhs.dist != rhs.dist)
                return lhs.dist < rhs.dist;
              if (lhs.enemy_near != rhs.enemy_near)
                return lhs.enemy_near < rhs.enemy_near;
              return lhs.side_tie < rhs.side_tie;
            });
  std::vector<int> targets;
  int target_limit = warm_opening_base_goal(M);
  for (const Candidate &c : candidates) {
    if (static_cast<int>(targets.size()) >= target_limit)
      break;
    targets.push_back(c.region);
  }
  return targets;
}

static int sub90_pending_opening_base_reserve(const GameState &S,
                                             const GameMap &M, const Paths &P,
                                             int planned_bases) {
  if (large_strategy_active(M))
    return 0;
  std::vector<int> targets = sub90_early_raid_opening_targets(S, M, P);
  int opening_goal =
      std::min(warm_opening_base_goal(M), static_cast<int>(targets.size()));
  if (planned_bases >= opening_goal)
    return 0;
  for (int target : targets) {
    if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
      continue;
    if (count_enemy_warriors_at(S, target, M) > 0)
      continue;
    if (has_target_worker_or_pending(S, M, target))
      return BASE_LEVELS[1].cost;
  }
  return 0;
}

static int hq_stationary_after_plans(const GameState &S, const GameMap &M,
                                     const Actions &a) {
  return count_my_stationary_at(S, M.my_hq, M) -
         planned_moves_from_region(a, S, M.my_hq);
}

static int committed_to_region(const GameState &S, const GameMap &M,
                               const Actions &a, int region) {
  int count = count_my_warriors_at(S, region, M) +
              planned_moves_to_region(a, region);
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::MOVING &&
        w.target == region) {
      ++count;
    }
  }
  return count;
}

static int select_sub90_early_raid_target(
    const GameState &S, const GameMap &M, const Paths &P, int current_target,
    const std::vector<const Warrior *> &raid_force, bool raid_has_launched) {
  const Building *current = find_building(S, current_target);
  if (current != nullptr && current->side != M.my_side &&
      current->type == BType::BASE && P.nxt[M.my_hq][current_target] != -1) {
    if (M.N >= 61 && M.N <= 79)
      return current_target;
    for (const Warrior *w : raid_force) {
      if (w->region == current_target ||
          (w->state == WState::MOVING && w->target == current_target)) {
        return current_target;
      }
    }
  }

  int best = -1;
  double best_score = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side || b.type != BType::BASE)
      continue;
    int nearest = 1000000;
    if (raid_force.empty()) {
      if (P.nxt[M.my_hq][b.region] != -1)
        nearest = P.hops[M.my_hq][b.region];
    } else {
      for (const Warrior *w : raid_force) {
        if (P.nxt[w->region][b.region] == -1)
          continue;
        nearest = std::min(nearest, P.hops[w->region][b.region]);
      }
    }
    if (nearest >= 1000000)
      continue;

    int center = M.N / 2;
    int center_hops = P.hops[center][b.region];
    int opp_hq_hops = P.hops[M.opp_hq][b.region];
    if (center_hops < 0 || opp_hq_hops < 0)
      continue;

    bool middle_band = M.N >= 61 && M.N <= 79;
    double hq_near_penalty =
        middle_band ? 0.0 : std::max(0, 4 - opp_hq_hops) * 300.0;
    if (!middle_band && opp_hq_hops <= 2)
      hq_near_penalty += 600.0;
    bool opening_center_priority = raid_force.empty() && !raid_has_launched;
    double center_weight =
        middle_band ? 0.0 : (opening_center_priority ? 1200.0 : 250.0);
    double force_weight =
        middle_band ? 1000.0 : (opening_center_priority ? 120.0 : 1000.0);
    double score = center_hops * center_weight + nearest * force_weight +
                   hq_near_penalty + b.hp * 5.0 + b.level * 70.0 +
                   count_enemy_warriors_at(S, b.region, M) * 100.0;
    if (score < best_score) {
      best_score = score;
      best = b.region;
    }
  }
  return best;
}

static int sub90_shortest_path_predecessor(const Paths &P, int from,
                                           int target) {
  if (from < 0 || target < 0 || from >= static_cast<int>(P.nxt.size()) ||
      target >= static_cast<int>(P.nxt.size())) {
    return -1;
  }
  if (from == target)
    return target;
  if (P.nxt[from][target] == -1)
    return -1;
  int cur = from;
  for (int guard = 0; guard < static_cast<int>(P.nxt.size()) + 2; ++guard) {
    int next = P.nxt[cur][target];
    if (next == -1)
      return -1;
    if (next == target)
      return cur;
    cur = next;
  }
  return -1;
}

static int sub90_staging_origin(const GameMap &M, const Paths &P, int target,
                                const std::vector<const Warrior *> &force) {
  int best = M.my_hq;
  int best_hops = P.hops[M.my_hq][target];
  int best_id = std::numeric_limits<int>::max();
  for (const Warrior *w : force) {
    if (w->id.side != M.my_side || P.nxt[w->region][target] == -1)
      continue;
    int hops = P.hops[w->region][target];
    if (best_hops < 0 || hops < best_hops ||
        (hops == best_hops && w->id.num < best_id)) {
      best = w->region;
      best_hops = hops;
      best_id = w->id.num;
    }
  }
  return best;
}

static int sub90_staging_region_for_target(
    const GameMap &M, const Paths &P, int target,
    const std::vector<const Warrior *> &force) {
  int origin = sub90_staging_origin(M, P, target, force);
  int stage = sub90_shortest_path_predecessor(P, origin, target);
  if (stage < 0)
    stage = sub90_shortest_path_predecessor(P, M.my_hq, target);
  return stage;
}

static int sub90_stage_committed_count(const GameState &S, const GameMap &M,
                                       const Actions &a, int stage,
                                       int target) {
  int count = committed_to_region(S, M, a, stage);
  if (target != stage)
    count += committed_to_region(S, M, a, target);
  return count;
}

static int sub90_stage_stationary_count(const GameState &S, const GameMap &M,
                                        int stage) {
  return count_my_stationary_at(S, stage, M);
}

static bool sub90_valid_enemy_base_target(const GameState &S, const GameMap &M,
                                          const Paths &P, int target) {
  const Building *b = find_building(S, target);
  return b != nullptr && b->side != M.my_side && b->type == BType::BASE &&
         P.nxt[M.my_hq][target] != -1;
}

static int sub90_staged_capture_need(const GameState &S, const GameMap &M,
                                     const Paths &P, int target) {
  const Building *b = find_building(S, target);
  if (b == nullptr || b->side == M.my_side || b->type != BType::BASE)
    return 1000000;
  int enemy_here = count_enemy_warriors_at(S, target, M);
  int enemy_support = std::max(0, enemy_near_region(S, M, P, target, 1) -
                                      enemy_here);
  int need = 4 + enemy_here;
  need += std::max(0, b->level - 1) * 2;
  need += std::max(0, b->hp - BASE_LEVELS[1].hp + 5) / 6;
  need += enemy_support / 2;
  return std::min(16, std::max(5, need));
}

static bool sub90_staged_capture_feasible(const GameState &S,
                                          const GameMap &M, const Paths &P,
                                          const Actions &a, int stage,
                                          int target) {
  if (stage < 0 || target < 0)
    return false;
  int committed = sub90_stage_committed_count(S, M, a, stage, target);
  int need = sub90_staged_capture_need(S, M, P, target);
  return committed >= need;
}

static bool add_sub90_early_stationary_group_move(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, const std::vector<const Warrior *> &group, int target,
    bool require_all);

static int select_warm_capture_target_excluding(
    const GameState &S, const GameMap &M, const Paths &P, int current_target,
    int turn, const std::set<int> &failed_targets) {
  if (failed_targets.count(current_target) == 0) {
    int kept = select_warm_capture_target(S, M, P, current_target, turn);
    if (kept >= 0 && failed_targets.count(kept) == 0)
      return kept;
  }

  int best = -1;
  double best_score = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side || b.type != BType::BASE ||
        failed_targets.count(b.region) > 0) {
      continue;
    }
    if (P.nxt[M.my_hq][b.region] == -1)
      continue;
    int stage = sub90_shortest_path_predecessor(P, M.my_hq, b.region);
    if (stage < 0)
      continue;
    int nearest = nearest_my_building_hops_any(S, M, P, stage);
    if (nearest > M.N)
      continue;
    int need = warm_capture_attack_need(S, M, P, b.region, turn);
    bool forward = is_front_half_region_for_my_side(M, b.region);
    double forward_bonus = forward ? (turn >= 80 ? 650.0 : 320.0) : 0.0;
    double back_penalty =
        (turn >= 80 && !is_front_half_region_for_my_side(M, b.region)) ? 320.0
                                                                       : 0.0;
    double score = nearest * 55.0 + P.hops[M.my_hq][stage] * 2.0 +
                   need * 75.0 + b.level * 55.0 + b.hp * 4.0 +
                   count_enemy_warriors_at(S, b.region, M) * 90.0 +
                   enemy_near_region(S, M, P, b.region, 1) * 35.0 +
                   back_penalty - forward_bonus;
    if (score < best_score) {
      best_score = score;
      best = b.region;
    }
  }
  return best;
}

static bool sub90_any_moving_to_region(const GameState &S, const GameMap &M,
                                       int region) {
  for (const auto &w : S.warriors) {
    if (w.id.side == M.my_side && w.state == WState::MOVING &&
        w.target == region) {
      return true;
    }
  }
  return false;
}

static bool sub90_force_has_moving_member(
    const std::vector<const Warrior *> &force) {
  for (const Warrior *w : force) {
    if (w->state == WState::MOVING)
      return true;
  }
  return false;
}

static bool sub90_force_has_front_half_member(
    const GameMap &M, const std::vector<const Warrior *> &force) {
  for (const Warrior *w : force) {
    if (is_front_half_region_for_my_side(M, w->region))
      return true;
  }
  return false;
}

static bool sub90_warrior_current_position_engaged(const GameState &S,
                                                   const GameMap &M,
                                                   const Warrior &w) {
  if (w.state != WState::STATIONARY)
    return false;
  if (count_enemy_warriors_at(S, w.region, M) > 0)
    return true;
  const Building *b = find_building(S, w.region);
  if (b != nullptr && b->side != M.my_side)
    return true;
  return false;
}

static bool sub90_force_current_position_engaged(
    const GameState &S, const GameMap &M,
    const std::vector<const Warrior *> &force) {
  for (const Warrior *w : force) {
    if (sub90_warrior_current_position_engaged(S, M, *w))
      return true;
  }
  return false;
}

static bool sub90_target_base_damaged(const GameState &S, const GameMap &M,
                                      int target);

static bool sub90_first_attack_center_enemy_base(const GameState &S,
                                                 const GameMap &M, int region,
                                                 bool raid_has_launched) {
  if (raid_has_launched || region != M.N / 2)
    return false;
  const Building *b = find_building(S, region);
  return b != nullptr && b->side != M.my_side && b->type == BType::BASE;
}

[[maybe_unused]] static bool add_sub90_warm_capture_staging_moves(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int capture_target, int need,
    const std::set<int> &capture_regions) {
  if (capture_target < 0 || need <= 0)
    return false;
  int stage = sub90_shortest_path_predecessor(P, M.my_hq, capture_target);
  if (stage < 0)
    return false;

  int committed = sub90_stage_committed_count(S, M, a, stage, capture_target);
  if (committed >= need || sub90_target_base_damaged(S, M, capture_target)) {
    std::vector<const Warrior *> staged;
    for (const auto &w : S.warriors) {
      if (w.id.side == M.my_side && w.state == WState::STATIONARY &&
          w.region == stage) {
        staged.push_back(&w);
      }
    }
    if (add_sub90_early_stationary_group_move(S, M, P, a, planned_gold, staged,
                                              capture_target, false)) {
      return true;
    }
  }

  int gather_need = std::max(0, need - committed);
  if (gather_need <= 0 || sub90_any_moving_to_region(S, M, stage))
    return false;
  int max_moves = std::min(gather_need, std::max(1, need / 2));
  (void)capture_regions;
  return add_surplus_moves_to_region(S, M, P, a, planned_gold, stage,
                                     max_moves);
}

static bool sub90_target_base_damaged(const GameState &S, const GameMap &M,
                                      int target) {
  const Building *b = find_building(S, target);
  if (b == nullptr || b->side == M.my_side || b->type != BType::BASE)
    return false;
  return b->hp < BASE_LEVELS[b->level].hp;
}

static bool sub90_raid_target_engaged(
    const GameState &S, const GameMap &M, int stage, int target,
    const std::vector<const Warrior *> &force) {
  if (target < 0)
    return false;
  if (sub90_target_base_damaged(S, M, target))
    return true;
  for (const Warrior *w : force) {
    if (w->region == target || w->region == stage ||
        (w->state == WState::MOVING && w->target == target)) {
      return true;
    }
  }
  return false;
}

static int select_sub90_early_raid_target_excluding(
    const GameState &S, const GameMap &M, const Paths &P, int current_target,
    const std::vector<const Warrior *> &raid_force, bool raid_has_launched,
    const std::set<int> &failed_targets) {
  if (failed_targets.count(current_target) == 0) {
    int kept = select_sub90_early_raid_target(S, M, P, current_target,
                                             raid_force, raid_has_launched);
    if (kept >= 0 && failed_targets.count(kept) == 0 &&
        !sub90_first_attack_center_enemy_base(S, M, kept,
                                              raid_has_launched))
      return kept;
  }

  int best = -1;
  double best_score = std::numeric_limits<double>::infinity();
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side || b.type != BType::BASE ||
        failed_targets.count(b.region) > 0) {
      continue;
    }
    if (sub90_first_attack_center_enemy_base(S, M, b.region,
                                             raid_has_launched))
      continue;
    if (P.nxt[M.my_hq][b.region] == -1)
      continue;
    int stage = sub90_staging_region_for_target(M, P, b.region, raid_force);
    if (stage < 0)
      continue;
    int nearest = raid_force.empty() ? P.hops[M.my_hq][stage] : 1000000;
    for (const Warrior *w : raid_force) {
      if (P.nxt[w->region][stage] != -1)
        nearest = std::min(nearest, P.hops[w->region][stage]);
    }
    if (nearest >= 1000000)
      continue;
    int need = sub90_staged_capture_need(S, M, P, b.region);
    double score = nearest * 800.0 + need * 120.0 + b.hp * 3.0 +
                   b.level * 50.0 +
                   count_enemy_warriors_at(S, b.region, M) * 100.0;
    if (score < best_score) {
      best_score = score;
      best = b.region;
    }
  }
  return best;
}

static bool sub90_all_enemy_bases_failed(const GameState &S, const GameMap &M,
                                         const std::set<int> &failed_targets) {
  bool has_enemy_base = false;
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side || b.type != BType::BASE)
      continue;
    has_enemy_base = true;
    if (failed_targets.count(b.region) == 0)
      return false;
  }
  return has_enemy_base;
}

static bool can_leave_for_sub90_early_raid(const GameState &S,
                                           const GameMap &M,
                                           const Actions &a,
                                           const Warrior &w) {
  if (w.id.side != M.my_side || w.state != WState::STATIONARY)
    return false;
  if (warrior_already_planned(a, w.id))
    return false;
  const Building *src = find_building(S, w.region);
  int after = count_my_stationary_at(S, w.region, M) -
              planned_moves_from_region(a, S, w.region);
  if (src == nullptr || src->side != M.my_side)
    return true;
  if (src->type == BType::HQ)
    return after > 1;
  return after > 1;
}

static bool is_sub90_early_forward_raid_warrior(const GameState &S,
                                                const GameMap &M,
                                                const Warrior &w) {
  if (w.id.side != M.my_side)
    return false;
  if (w.state == WState::MOVING)
    return true;
  if (w.region == M.my_hq)
    return false;
  const Building *src = find_building(S, w.region);
  if (src != nullptr && src->side == M.my_side)
    return false;
  return true;
}

static std::vector<const Warrior *> sub90_early_forward_raid_force(
    const GameState &S, const GameMap &M) {
  std::vector<const Warrior *> force;
  for (const auto &w : S.warriors) {
    if (is_sub90_early_forward_raid_warrior(S, M, w))
      force.push_back(&w);
  }
  return force;
}

static int sub90_early_stationary_move_cost_sum(const GameState &S,
                                                const GameMap &M,
                                                const Actions &a,
                                                const Paths &P,
                                                const std::vector<const Warrior *> &v,
                                                int target) {
  int sum = 0;
  for (const Warrior *w : v) {
    if (w->state != WState::STATIONARY || warrior_already_planned(a, w->id))
      continue;
    if (P.nxt[w->region][target] == -1)
      continue;
    sum += move_cost_to(S, M, target);
  }
  return sum;
}

static bool add_sub90_early_stationary_group_move(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, const std::vector<const Warrior *> &group, int target,
    bool require_all) {
  if (target < 0 || target >= M.N)
    return false;
  int movable = 0;
  for (const Warrior *w : group) {
    if (w->state != WState::STATIONARY || warrior_already_planned(a, w->id))
      continue;
    if (w->region == target || P.nxt[w->region][target] == -1)
      continue;
    if (!can_leave_for_sub90_early_raid(S, M, a, *w))
      continue;
    ++movable;
  }
  if (movable == 0)
    return false;
  int needed_gold =
      sub90_early_stationary_move_cost_sum(S, M, a, P, group, target);
  if (planned_gold < needed_gold)
    return false;

  size_t mark = a.moves.size();
  int gold_mark = planned_gold;
  int issued = 0;
  for (const Warrior *w : group) {
    if (w->state != WState::STATIONARY || warrior_already_planned(a, w->id))
      continue;
    if (w->region == target || P.nxt[w->region][target] == -1)
      continue;
    if (!can_leave_for_sub90_early_raid(S, M, a, *w))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, target))
      continue;
    ++issued;
  }
  if (!require_all || issued == movable)
    return issued > 0;
  a.moves.resize(mark);
  planned_gold = gold_mark;
  return false;
}

static bool add_sub90_early_return_force_to_hq(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold) {
  std::vector<const Warrior *> force;
  for (const Warrior *w : sub90_early_forward_raid_force(S, M)) {
    if (w->state == WState::STATIONARY &&
        !sub90_warrior_current_position_engaged(S, M, *w))
      force.push_back(w);
  }
  return add_sub90_early_stationary_group_move(S, M, P, a, planned_gold, force,
                                               M.my_hq, false);
}

static bool add_sub90_early_launch_from_hq(const GameState &S,
                                           const GameMap &M, const Paths &P,
                                           Actions &a, int &planned_gold,
                                           int target,
                                           int min_attackers = 5,
                                           std::vector<int> *launched_ids =
                                               nullptr) {
  int hq_ready = hq_stationary_after_plans(S, M, a);
  if (hq_ready - 1 < min_attackers)
    return false;
  std::vector<const Warrior *> hq_group;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY ||
        w.region != M.my_hq || warrior_already_planned(a, w.id)) {
      continue;
    }
    hq_group.push_back(&w);
  }
  std::sort(hq_group.begin(), hq_group.end(),
            [](const Warrior *lhs, const Warrior *rhs) {
              return lhs->id.num < rhs->id.num;
            });
  int launch_count = hq_ready - 1;
  if (static_cast<int>(hq_group.size()) < launch_count)
    return false;
  int needed_gold = 0;
  for (int i = 0; i < launch_count; ++i) {
    if (P.nxt[hq_group[i]->region][target] == -1)
      return false;
    needed_gold += move_cost_to(S, M, target);
  }
  if (planned_gold < needed_gold)
    return false;
  size_t mark = a.moves.size();
  int gold_mark = planned_gold;
  int issued = 0;
  std::vector<int> local_launched;
  for (const Warrior *w : hq_group) {
    if (issued >= launch_count)
      break;
    if (!can_leave_for_sub90_early_raid(S, M, a, *w))
      continue;
    if (!add_move_with_large_waypoint(S, M, P, a, planned_gold, *w, target))
      continue;
    local_launched.push_back(w->id.num);
    ++issued;
  }
  if (issued == launch_count) {
    if (launched_ids != nullptr)
      *launched_ids = local_launched;
    return true;
  }
  a.moves.resize(mark);
  planned_gold = gold_mark;
  return false;
}

static void prune_sub90_wave_targets(const GameState &S, const GameMap &M,
                                     std::map<int, int> &wave_target_by_id) {
  std::set<int> alive;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    alive.insert(w.id.num);
    if (w.state == WState::STATIONARY && w.region == M.my_hq)
      wave_target_by_id.erase(w.id.num);
  }
  for (auto it = wave_target_by_id.begin(); it != wave_target_by_id.end();) {
    if (alive.count(it->first) == 0)
      it = wave_target_by_id.erase(it);
    else
      ++it;
  }
}

static std::set<int>
active_sub90_wave_targets(const GameState &S, const GameMap &M,
                          const std::map<int, int> &wave_target_by_id) {
  std::set<int> targets;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    auto it = wave_target_by_id.find(w.id.num);
    if (it == wave_target_by_id.end())
      continue;
    if (w.state == WState::STATIONARY && w.region == M.my_hq)
      continue;
    targets.insert(it->second);
  }
  return targets;
}

static std::vector<const Warrior *>
sub90_wave_members_for_target(const GameState &S, const GameMap &M,
                              const std::map<int, int> &wave_target_by_id,
                              int target) {
  std::vector<const Warrior *> members;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side)
      continue;
    auto it = wave_target_by_id.find(w.id.num);
    if (it == wave_target_by_id.end() || it->second != target)
      continue;
    if (w.state == WState::STATIONARY && w.region == M.my_hq)
      continue;
    members.push_back(&w);
  }
  return members;
}

static bool add_sub90_depleted_wave_return(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, const std::map<int, int> &wave_target_by_id) {
  std::set<int> targets = active_sub90_wave_targets(S, M, wave_target_by_id);
  for (int target : targets) {
    std::vector<const Warrior *> members =
        sub90_wave_members_for_target(S, M, wave_target_by_id, target);
    if (members.empty() || static_cast<int>(members.size()) > 4)
      continue;
    bool has_moving = sub90_force_has_moving_member(members);
    if (has_moving)
      continue;
    bool engaged = sub90_force_current_position_engaged(S, M, members);
    if (target == M.opp_hq) {
      for (const Warrior *w : members) {
        if (w->region == M.opp_hq ||
            (w->state == WState::MOVING && w->target == M.opp_hq)) {
          engaged = true;
          break;
        }
      }
    } else if (!engaged) {
      int stage = sub90_staging_region_for_target(M, P, target, members);
      engaged = sub90_raid_target_engaged(S, M, stage, target, members);
    }
    if (engaged)
      continue;
    if (add_sub90_early_stationary_group_move(S, M, P, a, planned_gold,
                                              members, M.my_hq, false))
      return true;
  }
  return false;
}

static bool add_sub90_independent_hq_wave(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int &raid_target, bool &raid_has_launched,
    std::map<int, int> &wave_target_by_id,
    const std::set<int> &failed_targets) {
  int launch_need = warm_rally_min_attackers(M);
  if (hq_stationary_after_plans(S, M, a) - 1 < launch_need)
    return false;

  std::set<int> excluded = failed_targets;
  std::set<int> active_targets =
      active_sub90_wave_targets(S, M, wave_target_by_id);
  excluded.insert(active_targets.begin(), active_targets.end());

  std::vector<const Warrior *> empty_force;
  int target = select_sub90_early_raid_target_excluding(
      S, M, P, -1, empty_force, raid_has_launched, excluded);
  if (target < 0) {
    if (count_enemy_bases(S, M) <= 0)
      target = M.opp_hq;
    else
      return false;
  }

  if (target != M.opp_hq) {
    launch_need =
        std::max(launch_need, sub90_staged_capture_need(S, M, P, target));
    if (hq_stationary_after_plans(S, M, a) - 1 < launch_need)
      return false;
  }

  std::vector<int> launched_ids;
  if (!add_sub90_early_launch_from_hq(S, M, P, a, planned_gold, target,
                                      launch_need, &launched_ids))
    return false;
  for (int id : launched_ids)
    wave_target_by_id[id] = target;
  raid_target = target;
  raid_has_launched = true;
  return true;
}

static bool sub90_large_post_first_rally_hq2_gate_active(
    const GameMap &M, const Building *hq, bool raid_has_launched) {
  return forced_warm_large_map(M) && M.N >= 95 && raid_has_launched &&
         hq != nullptr && hq->level == 1;
}

static bool add_sub90_early_five_unit_raid(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, int &planned_bases,
    int &raid_target, const Building *hq, int turn, bool &raid_returning,
    bool &raid_has_launched) {
  if (large_strategy_active(M) || hq == nullptr)
    return false;
  (void)turn;

  static std::set<int> staging_failed_targets;
  static std::map<int, int> wave_target_by_id;
  int enemy_bases = count_enemy_bases(S, M);
  prune_sub90_wave_targets(S, M, wave_target_by_id);
  if (enemy_bases <= 0) {
    staging_failed_targets.clear();
    wave_target_by_id.clear();
  }

  std::vector<int> opening_targets =
      sub90_early_raid_opening_targets(S, M, P);
  int opening_goal =
      std::min(warm_opening_base_goal(M),
               static_cast<int>(opening_targets.size()));
  auto add_opening_reserved_train = [&](int wanted_train) {
    if (sub90_large_post_first_rally_hq2_gate_active(M, hq,
                                                     raid_has_launched))
      return false;
    int reserve = sub90_pending_opening_base_reserve(S, M, P, planned_bases);
    return add_train_if_needed_with_reserve(S, M, a, planned_gold,
                                            wanted_train, reserve);
  };
  auto apply_post_first_rally_hq2_gate = [&]() {
    if (!sub90_large_post_first_rally_hq2_gate_active(M, hq,
                                                      raid_has_launched))
      return false;
    if (!used_upgrades.count(hq->region) &&
        planned_gold >= HQ_LEVELS[2].upgrade_cost) {
      add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
    }
    return true;
  };
  for (int target : opening_targets) {
    if (planned_bases >= opening_goal)
      break;
    if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
      continue;
    if (count_my_stationary_at(S, target, M) > 0 &&
        count_enemy_warriors_at(S, target, M) == 0) {
      if (add_base_build(S, M, a, used_upgrades, planned_gold, planned_bases,
                         target)) {
        if (planned_bases >= opening_goal && a.train_n == 0)
          add_opening_reserved_train(1);
        return true;
      }
    }
  }

  int workers_sent = 0;
  for (int target : opening_targets) {
    if (planned_bases + workers_sent >= opening_goal)
      break;
    if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
      continue;
    if (has_worker_or_pending_for_target(S, M, target))
      continue;
    if (add_worker_move_to_target(S, M, P, a, planned_gold, target, true))
      ++workers_sent;
  }
  if (workers_sent > 0)
    return true;

  if (planned_bases < opening_goal) {
    bool waiting = false;
    for (int target : opening_targets) {
      if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
        continue;
      if (has_target_worker_or_pending(S, M, target))
        waiting = true;
    }
    if (waiting)
      return true;
  }

  std::vector<const Warrior *> forward_force =
      sub90_early_forward_raid_force(S, M);
  bool hq2_gate_active = apply_post_first_rally_hq2_gate();
  if (enemy_bases > 0) {
    if (!hq2_gate_active) {
      add_sub90_independent_hq_wave(S, M, P, a, planned_gold, raid_target,
                                    raid_has_launched, wave_target_by_id,
                                    staging_failed_targets);
    }
    if (add_sub90_depleted_wave_return(S, M, P, a, planned_gold,
                                       wave_target_by_id)) {
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return true;
    }
  }
  if (enemy_bases <= 0) {
    int hq_attack_need =
        observed_hq_level(S, M, opposite(M.my_side)) >= 2 ? 10 : 5;
    if (forced_warm_large_map(M))
      hq_attack_need = warm_rally_min_attackers(M);
    else
      hq_attack_need = std::max(hq_attack_need, warm_rally_min_attackers(M));
    bool hq_wave_launched = false;
    if (!hq2_gate_active && !forward_force.empty() &&
        hq_stationary_after_plans(S, M, a) - 1 >= hq_attack_need) {
      hq_wave_launched = add_sub90_early_launch_from_hq(
          S, M, P, a, planned_gold, M.opp_hq, hq_attack_need);
      if (hq_wave_launched)
        raid_has_launched = true;
    }
    raid_returning = false;
    if (!forward_force.empty()) {
      bool hq_force_moving = sub90_force_has_moving_member(forward_force);
      bool at_enemy_hq = false;
      for (const Warrior *w : forward_force) {
        if (w->region == M.opp_hq) {
          at_enemy_hq = true;
          break;
        }
      }
      bool current_engaged =
          sub90_force_current_position_engaged(S, M, forward_force);
      if (static_cast<int>(forward_force.size()) <= 4 && !hq_force_moving &&
          !at_enemy_hq && !current_engaged) {
        raid_returning = true;
        bool issued =
            add_sub90_early_return_force_to_hq(S, M, P, a, planned_gold);
        if (a.train_n == 0)
          add_opening_reserved_train(1);
        return issued || a.train_n > 0 || true;
      }
      bool issued = add_sub90_early_stationary_group_move(
          S, M, P, a, planned_gold, forward_force, M.opp_hq, true);
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return issued || a.train_n > 0 || true;
    }
    bool issued = false;
    if (!hq2_gate_active) {
      issued =
          add_sub90_early_launch_from_hq(S, M, P, a, planned_gold, M.opp_hq,
                                         hq_attack_need);
    }
    if (issued)
      raid_has_launched = true;
    if (!issued && a.train_n == 0)
      add_opening_reserved_train(1);
    return true;
  }

  if (raid_returning) {
    if (!forward_force.empty()) {
      bool issued = add_sub90_early_return_force_to_hq(S, M, P, a, planned_gold);
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return issued || a.train_n > 0 || true;
    }
    raid_returning = false;
    if (hq_stationary_after_plans(S, M, a) >= 6)
      staging_failed_targets.clear();
  }

  if (forward_force.empty() && hq_stationary_after_plans(S, M, a) >= 6)
    staging_failed_targets.clear();

  if (sub90_all_enemy_bases_failed(S, M, staging_failed_targets)) {
    staging_failed_targets.clear();
    raid_returning = !forward_force.empty();
    if (raid_returning) {
      bool issued = add_sub90_early_return_force_to_hq(S, M, P, a, planned_gold);
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return issued || a.train_n > 0 || true;
    }
    if (a.train_n == 0)
      add_opening_reserved_train(1);
    return true;
  }

  int attempts = std::max(1, enemy_bases + 1);
  while (attempts-- > 0) {
    bool force_moving = sub90_force_has_moving_member(forward_force);
    if (!force_moving || !sub90_valid_enemy_base_target(S, M, P, raid_target)) {
      raid_target = select_sub90_early_raid_target_excluding(
          S, M, P, raid_target, forward_force, raid_has_launched,
          staging_failed_targets);
    }
    const Building *target_building = find_building(S, raid_target);
    if (target_building == nullptr || target_building->side == M.my_side ||
        target_building->type != BType::BASE) {
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return true;
    }

    int stage =
        sub90_staging_region_for_target(M, P, raid_target, forward_force);
    if (stage < 0) {
      staging_failed_targets.insert(raid_target);
      raid_target = -1;
      continue;
    }

    if (!forward_force.empty()) {
      bool has_moving_force = sub90_force_has_moving_member(forward_force);

      if (sub90_staged_capture_feasible(S, M, P, a, stage, raid_target)) {
        bool issued = add_sub90_early_stationary_group_move(
            S, M, P, a, planned_gold, forward_force, raid_target, true);
        if (a.train_n == 0)
          add_opening_reserved_train(1);
        return issued || a.train_n > 0 || true;
      }

      int staged = sub90_stage_committed_count(S, M, a, stage, raid_target);
      int stage_stationary = sub90_stage_stationary_count(S, M, stage);
      int need = sub90_staged_capture_need(S, M, P, raid_target);
      bool target_engaged =
          sub90_raid_target_engaged(S, M, stage, raid_target, forward_force);
      if (!has_moving_force && stage_stationary > 0 && staged < need &&
          !target_engaged) {
        staging_failed_targets.insert(raid_target);
        raid_target = -1;
        continue;
      }

      bool current_engaged =
          sub90_force_current_position_engaged(S, M, forward_force);
      if (static_cast<int>(forward_force.size()) <= 4 && !has_moving_force &&
          !target_engaged && !current_engaged) {
        raid_returning = true;
        bool issued =
            add_sub90_early_return_force_to_hq(S, M, P, a, planned_gold);
        if (a.train_n == 0)
          add_opening_reserved_train(1);
        return issued || a.train_n > 0 || true;
      }

      bool issued = add_sub90_early_stationary_group_move(
          S, M, P, a, planned_gold, forward_force, raid_target, true);
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return issued || a.train_n > 0 || true;
    }

    int need = sub90_staged_capture_need(S, M, P, raid_target);
    int launch_need = std::max(need, warm_rally_min_attackers(M));
    if (hq2_gate_active && forward_force.empty())
      return true;
    if (hq_stationary_after_plans(S, M, a) - 1 < launch_need) {
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return true;
    }
    std::vector<int> launched_ids;
    bool issued = add_sub90_early_launch_from_hq(
        S, M, P, a, planned_gold, raid_target, launch_need, &launched_ids);
    if (issued) {
      raid_has_launched = true;
      for (int id : launched_ids)
        wave_target_by_id[id] = raid_target;
    }
    if (!issued && a.train_n == 0)
      add_opening_reserved_train(1);
    return true;
  }

  if (!forward_force.empty()) {
    staging_failed_targets.clear();
    bool fallback_force_moving = sub90_force_has_moving_member(forward_force);
    bool current_engaged =
        sub90_force_current_position_engaged(S, M, forward_force);
    if (static_cast<int>(forward_force.size()) <= 4 &&
        !fallback_force_moving && !current_engaged) {
      raid_returning = true;
      bool issued = add_sub90_early_return_force_to_hq(S, M, P, a, planned_gold);
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return issued || a.train_n > 0 || true;
    }
    if (sub90_force_has_front_half_member(M, forward_force)) {
      raid_returning = false;
      bool issued = add_sub90_early_stationary_group_move(
          S, M, P, a, planned_gold, forward_force, M.opp_hq, true);
      if (a.train_n == 0)
        add_opening_reserved_train(1);
      return issued || a.train_n > 0 || true;
    }
    raid_returning = true;
    bool issued = add_sub90_early_return_force_to_hq(S, M, P, a, planned_gold);
    if (a.train_n == 0)
      add_opening_reserved_train(1);
    return issued || a.train_n > 0 || true;
  }
  staging_failed_targets.clear();
  if (a.train_n == 0)
    add_opening_reserved_train(1);
  return true;
}

struct WarmBaseThreat {
  bool active = false;
  int region = -1;
  int enemy_close = 0;
  int enemy_near = 0;
  int defender_need = 0;
};

static WarmBaseThreat detect_sub90_base_threat(const GameState &S,
                                               const GameMap &M,
                                               const Paths &P) {
  WarmBaseThreat best;
  int best_score = -1;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    int enemy_here = count_enemy_warriors_at(S, b.region, M);
    int close = enemy_near_region(S, M, P, b.region, 1);
    int near = enemy_near_region(S, M, P, b.region, 2);
    if (enemy_here == 0 && close == 0 && near < 2)
      continue;
    int own_here = count_my_stationary_at(S, b.region, M);
    int need = std::max(2, enemy_here + close + near / 2 + (b.hp <= 3 ? 2 : 0));
    int score = enemy_here * 100 + close * 45 + near * 15 + (6 - b.hp) * 8 -
                own_here * 20;
    if (own_here < need || enemy_here > 0 || b.hp <= 3) {
      if (score > best_score) {
        best_score = score;
        best.active = true;
        best.region = b.region;
        best.enemy_close = close;
        best.enemy_near = near;
        best.defender_need = need;
      }
    }
  }
  return best;
}

static bool can_borrow_for_warm_base_defense(const GameState &S,
                                             const GameMap &M,
                                             const Actions &a,
                                             const Warrior &w,
                                             int target) {
  if (w.id.side != M.my_side || w.state != WState::STATIONARY)
    return false;
  if (warrior_already_planned(a, w.id))
    return false;
  if (is_committed_hq_assault_warrior(w, M))
    return false;
  const Building *src = find_building(S, w.region);
  int after = count_my_stationary_at(S, w.region, M) -
              planned_moves_from_region(a, S, w.region);
  if (src == nullptr || src->side != M.my_side)
    return true;
  if (src->type == BType::HQ)
    return after > 1 && count_enemy_warriors_at(S, M.my_hq, M) == 0;
  if (w.region == target)
    return false;
  return after > 1;
}

static bool apply_sub90_warm_base_defense(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    std::set<int> &used_upgrades, int &planned_gold, const Building *hq) {
  WarmBaseThreat threat = detect_sub90_base_threat(S, M, P);
  if (!threat.active)
    return false;

  bool issued = false;
  const Building *base = find_building(S, threat.region);
  if (base != nullptr && count_enemy_warriors_at(S, threat.region, M) == 0 &&
      (base->hp < base->current_hp() || threat.enemy_close >= 2)) {
    issued |= add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                                   threat.region);
  }

  int committed = committed_my_count_at(S, a, threat.region, M);
  int need_moves = std::min(8, std::max(0, threat.defender_need - committed));
  std::vector<const Warrior *> defenders;
  for (const auto &w : S.warriors) {
    if (!can_borrow_for_warm_base_defense(S, M, a, w, threat.region))
      continue;
    if (w.region == threat.region)
      continue;
    if (P.nxt[w.region][threat.region] == -1)
      continue;
    defenders.push_back(&w);
  }
  std::sort(defenders.begin(), defenders.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][threat.region] !=
                  P.hops[rhs->region][threat.region]) {
                return P.hops[lhs->region][threat.region] <
                       P.hops[rhs->region][threat.region];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  int moved = 0;
  for (const Warrior *w : defenders) {
    if (moved >= need_moves)
      break;
    int cost = move_cost_to(S, M, threat.region);
    if (planned_gold < cost)
      break;
    if (!can_borrow_for_warm_base_defense(S, M, a, *w, threat.region))
      continue;
    a.moves.emplace_back(w->id, threat.region);
    planned_gold -= cost;
    ++moved;
    issued = true;
  }

  if (hq != nullptr) {
    int cap = HQ_LEVELS[std::max(1, std::min(HQ_MAX_LEVEL, hq->level))].train_cap;
    issued |= add_train_if_needed(S, M, a, planned_gold, cap);
  }
  return issued;
}

struct Sub90HqBaseDefenseThreat {
  bool active = false;
  int region = -1;
  int priority = 99;
  int hq_hops = 1000000;
};

static int sub90_hq_force_base_threat_priority(const GameState &S,
                                               const GameMap &M,
                                               const Paths &P, int region) {
  const Building *b = find_building(S, region);
  if (b == nullptr || b->side != M.my_side || b->type != BType::BASE)
    return 0;

  bool enemy_inside = false;
  bool enemy_adjacent = false;
  Side enemy = opposite(M.my_side);
  for (const auto &w : S.warriors) {
    if (w.id.side != enemy)
      continue;
    if (w.region == region) {
      enemy_inside = true;
      break;
    }
    if (P.hops[w.region][region] == 1)
      enemy_adjacent = true;
  }
  if (enemy_inside)
    return 1;
  if (enemy_adjacent)
    return 2;
  return 0;
}

static Sub90HqBaseDefenseThreat select_sub90_hq_force_base_threat(
    const GameState &S, const GameMap &M, const Paths &P) {
  Sub90HqBaseDefenseThreat best;
  for (const auto &b : S.buildings) {
    if (b.side != M.my_side || b.type != BType::BASE)
      continue;
    int priority = sub90_hq_force_base_threat_priority(S, M, P, b.region);
    if (priority == 0)
      continue;
    int hq_hops = P.hops[M.my_hq][b.region];
    if (hq_hops < 0)
      continue;
    if (!best.active || priority < best.priority ||
        (priority == best.priority && hq_hops < best.hq_hops) ||
        (priority == best.priority && hq_hops == best.hq_hops &&
         b.region < best.region)) {
      best.active = true;
      best.region = b.region;
      best.priority = priority;
      best.hq_hops = hq_hops;
    }
  }
  return best;
}

static bool add_sub90_hq_force_base_defense_return(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, std::set<int> &defender_ids) {
  bool still_returning = false;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || !defender_ids.count(w.id.num))
      continue;
    if (w.state == WState::MOVING) {
      still_returning = true;
      continue;
    }
    if (w.region == M.my_hq)
      continue;
    still_returning = true;
    if (warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.my_hq] == -1)
      continue;
    int cost = move_cost_to(S, M, M.my_hq);
    if (planned_gold < cost)
      continue;
    a.moves.emplace_back(w.id, M.my_hq);
    planned_gold -= cost;
  }
  if (!still_returning)
    defender_ids.clear();
  return still_returning;
}

static bool apply_sub90_hq_force_base_defense(
    const GameState &S, const GameMap &M, const Paths &P, Actions &a,
    int &planned_gold, int &active_target, std::set<int> &defender_ids) {
  if (large_strategy_active(M))
    return false;

  Sub90HqBaseDefenseThreat threat =
      select_sub90_hq_force_base_threat(S, M, P);
  int active_priority =
      active_target >= 0
          ? sub90_hq_force_base_threat_priority(S, M, P, active_target)
          : 0;

  if (active_target >= 0 && active_priority == 0) {
    if (add_sub90_hq_force_base_defense_return(S, M, P, a, planned_gold,
                                               defender_ids)) {
      return true;
    }
    active_target = -1;
  }

  if (!threat.active)
    return false;

  if (active_target < 0 || threat.priority < active_priority ||
      (threat.priority == active_priority && threat.region != active_target)) {
    active_target = threat.region;
  }

  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY ||
        w.region != M.my_hq || warrior_already_planned(a, w.id)) {
      continue;
    }
    if (P.nxt[w.region][active_target] == -1)
      continue;
    int cost = move_cost_to(S, M, active_target);
    if (planned_gold < cost)
      break;
    a.moves.emplace_back(w.id, active_target);
    planned_gold -= cost;
    defender_ids.insert(w.id.num);
  }

  return true;
}

static bool add_sub90_warm_staged_hq_finish(const GameState &S,
                                            const GameMap &M,
                                            const Paths &P, Actions &a,
                                            int &planned_gold, int turn) {
  if (turn < 115)
    return false;
  if (hq_assault_urgent_threat_active(S, M, P))
    return false;

  int rally_region = select_hq_assault_rally_base(S, M, P);
  if (rally_region < 0)
    return false;

  int threshold = 16;
  if (turn >= 145)
    threshold = 12;
  if (turn >= 165)
    threshold = 9;
  if (turn >= 180)
    threshold = 7;
  if (turn >= 190)
    threshold = 5;
  if (turn >= 195)
    threshold = 4;
  if (count_forward_my_bases(S, M, P) > 0)
    threshold = std::min(threshold, turn >= 180 ? 6 : 10);
  if (count_enemy_bases(S, M) <= 3)
    threshold = std::min(threshold, turn >= 170 ? 5 : 7);

  int ready = count_hq_assault_ready_at(S, M, a, rally_region);
  int reserve = reserve_need_at_region(S, M, rally_region);
  int launchable = std::max(0, ready - reserve);
  if (launchable >= threshold) {
    std::vector<const Warrior *> attackers;
    for (const auto &w : S.warriors) {
      if (w.id.side != M.my_side || w.state != WState::STATIONARY)
        continue;
      if (w.region != rally_region || warrior_already_planned(a, w.id))
        continue;
      if (P.nxt[w.region][M.opp_hq] == -1)
        continue;
      attackers.push_back(&w);
    }
    std::sort(attackers.begin(), attackers.end(),
              [](const Warrior *lhs, const Warrior *rhs) {
                if (lhs->hp != rhs->hp)
                  return lhs->hp > rhs->hp;
                return lhs->id.num < rhs->id.num;
              });

    bool issued = false;
    int issued_count = 0;
    for (const Warrior *w : attackers) {
      if (issued_count >= launchable)
        break;
      int cost = move_cost_to(S, M, M.opp_hq);
      if (planned_gold < cost)
        break;
      if (!can_leave_late_all_in_source(S, M, a, w->region))
        continue;
      a.moves.emplace_back(w->id, M.opp_hq);
      planned_gold -= cost;
      ++issued_count;
      issued = true;
    }
    if (issued) {
      g_hq_assault_committed = true;
      g_hq_assault_rally_region = -1;
      add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                                M.opp_hq);
      return true;
    }
  }

  int inbound = count_hq_assault_inbound_to(S, M, rally_region);
  int gather_need = std::max(0, threshold + 5 - ready - inbound);
  int max_gather = turn >= 135 ? 16 : 8;
  if (add_hq_assault_gather_moves(S, M, P, a, planned_gold, rally_region,
                                  std::min(max_gather, gather_need))) {
    g_hq_assault_rally_region = rally_region;
    return true;
  }

  return ready + inbound >= std::max(4, threshold / 2);
}

static bool add_sub90_warm_hq_finish(const GameState &S, const GameMap &M,
                                     const Paths &P, Actions &a,
                                     int &planned_gold, int turn,
                                     const std::set<int> &capture_regions) {
  int forward_bases = count_forward_my_bases(S, M, P);
  int enemy_bases = count_enemy_bases(S, M);
  bool forward_capture_seen = false;
  for (int r : capture_regions) {
    if (is_my_base_at(S, M, r)) {
      forward_capture_seen = true;
      break;
    }
  }
  if (turn < 132)
    return false;
  if (!forward_capture_seen && forward_bases == 0 && enemy_bases > 2 &&
      turn < 165)
    return false;

  std::vector<const Warrior *> attackers;
  int hp = 0;
  for (const auto &w : S.warriors) {
    if (w.id.side != M.my_side || w.state != WState::STATIONARY)
      continue;
    if (w.region == M.opp_hq || warrior_already_planned(a, w.id))
      continue;
    if (P.nxt[w.region][M.opp_hq] == -1)
      continue;
    if (!can_leave_late_all_in_source(S, M, a, w.region))
      continue;
    attackers.push_back(&w);
    hp += std::max(1, w.hp);
  }

  int min_count = 14;
  if (turn >= 150)
    min_count = 10;
  if (turn >= 170)
    min_count = 8;
  if (turn >= 188)
    min_count = 5;
  if (enemy_bases <= 2 && turn >= 140)
    min_count = std::min(min_count, 6);
  if (forward_capture_seen && turn >= 132)
    min_count = std::min(min_count, 8);
  if (static_cast<int>(attackers.size()) < min_count && hp < min_count * 4)
    return false;

  std::sort(attackers.begin(), attackers.end(),
            [&](const Warrior *lhs, const Warrior *rhs) {
              if (P.hops[lhs->region][M.opp_hq] !=
                  P.hops[rhs->region][M.opp_hq]) {
                return P.hops[lhs->region][M.opp_hq] <
                       P.hops[rhs->region][M.opp_hq];
              }
              if (lhs->hp != rhs->hp)
                return lhs->hp > rhs->hp;
              return lhs->id.num < rhs->id.num;
            });

  bool issued = false;
  for (const Warrior *w : attackers) {
    int cost = move_cost_to(S, M, M.opp_hq);
    if (planned_gold < cost)
      break;
    if (!can_leave_late_all_in_source(S, M, a, w->region))
      continue;
    a.moves.emplace_back(w->id, M.opp_hq);
    planned_gold -= cost;
    issued = true;
  }
  if (issued) {
    g_hq_assault_committed = true;
    g_hq_assault_rally_region = -1;
    add_common_base_surplus_attack_join_moves(S, M, P, a, planned_gold,
                                              M.opp_hq);
  }
  return issued;
}

static Actions decide_sub90_warm_table(const GameState &S, const GameMap &M,
                                       const Paths &P, int turn) {
  Actions a;
  std::set<int> used_upgrades;
  int planned_gold = std::max(0, S.gold);

  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr)
    return a;

  static int warm_capture_target = -1;
  static std::set<int> warm_capture_regions;
  static std::set<int> warm_capture_failed_targets;
  static std::set<int> ever_owned_base_regions;
  static int early_raid_target = -1;
  static bool early_raid_returning = false;
  static bool early_raid_has_launched = false;
  static int hq_force_base_defense_target = -1;
  static std::set<int> hq_force_base_defenders;
  if (turn <= 1) {
    warm_capture_target = -1;
    warm_capture_regions.clear();
    warm_capture_failed_targets.clear();
    ever_owned_base_regions.clear();
    early_raid_target = -1;
    early_raid_returning = false;
    early_raid_has_launched = false;
    hq_force_base_defense_target = -1;
    hq_force_base_defenders.clear();
    g_hq_assault_committed = false;
    g_hq_assault_rally_region = -1;
  }

  for (const auto &b : S.buildings) {
    if (b.side == M.my_side && b.type == BType::BASE)
      ever_owned_base_regions.insert(b.region);
  }

  int current_my_bases = count_my_bases(S, M);
  int planned_bases = current_my_bases;

  bool enemy_inside_hq = count_enemy_warriors_at(S, M.my_hq, M) > 0;
  if (enemy_inside_hq) {
    add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
    for (const auto &w : S.warriors) {
      if (w.id.side != M.my_side || w.state != WState::STATIONARY)
        continue;
      if (w.region == M.my_hq || warrior_already_planned(a, w.id))
        continue;
      if (is_committed_hq_assault_warrior(w, M))
        continue;
      if (P.nxt[w.region][M.my_hq] == -1)
        continue;
      int cost = move_cost_to(S, M, M.my_hq);
      if (planned_gold < cost)
        break;
      a.moves.emplace_back(w.id, M.my_hq);
      planned_gold -= cost;
    }
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (apply_sub90_warm_hq_defense(S, M, P, a, used_upgrades, planned_gold,
                                  hq)) {
    return a;
  }

  if (apply_sub90_hq_force_base_defense(
          S, M, P, a, planned_gold, hq_force_base_defense_target,
          hq_force_base_defenders)) {
    add_train_if_needed_with_reserve(
        S, M, a, planned_gold, HQ_LEVELS[hq->level].train_cap,
        sub90_pending_opening_base_reserve(S, M, P, planned_bases));
    return a;
  }

  if (!large_strategy_active(M) && turn <= 6 && current_my_bases == 1 &&
      sub90_early_hq_rush_signal(S, M, P, turn)) {
    add_train_if_needed_with_reserve(
        S, M, a, planned_gold, HQ_LEVELS[hq->level].train_cap,
        sub90_pending_opening_base_reserve(S, M, P, planned_bases));
    return a;
  }

  if (add_sub90_post_defense_base_refill(S, M, P, a, planned_gold, hq)) {
    add_train_if_needed_with_reserve(
        S, M, a, planned_gold, HQ_LEVELS[hq->level].train_cap,
        sub90_pending_opening_base_reserve(S, M, P, planned_bases));
    return a;
  }

  if (add_sub90_early_five_unit_raid(S, M, P, a, used_upgrades,
                                     planned_gold, planned_bases,
                                     early_raid_target, hq, turn,
                                     early_raid_returning,
                                     early_raid_has_launched)) {
    return a;
  }

  add_forward_base_builds(S, M, a, used_upgrades, planned_gold, planned_bases,
                          warm_capture_regions);
  if (!a.upgrades.empty()) {
    add_train_if_needed(S, M, a, planned_gold, 1);
    return a;
  }
  if (captured_base_build_waiting(S, M, used_upgrades,
                                  warm_capture_regions)) {
    return a;
  }

  std::vector<int> initial_targets = sub90_warm_initial_targets(S, M, P);
  int warm_base_goal = std::min(sub90_warm_base_goal(M),
                                static_cast<int>(initial_targets.size()));
  for (int target : initial_targets) {
    if (planned_bases >= warm_base_goal)
      break;
    if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
      continue;
    if (count_my_stationary_at(S, target, M) > 0 &&
        count_enemy_warriors_at(S, target, M) == 0) {
      add_base_build(S, M, a, used_upgrades, planned_gold, planned_bases,
                     target);
    }
  }
  if (!a.upgrades.empty()) {
    if (planned_bases >= 2)
      add_train_if_needed(S, M, a, planned_gold, 1);
    return a;
  }

  bool waiting_initial_build =
      sub90_waiting_initial_build(S, M, initial_targets, planned_bases);
  if (waiting_initial_build && planned_gold < BASE_LEVELS[1].cost &&
      turn < 90) {
    return a;
  }

  int workers_sent = 0;
  for (int target : initial_targets) {
    if (planned_bases + workers_sent >= warm_base_goal)
      break;
    if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
      continue;
    if (has_worker_or_pending_for_target(S, M, target))
      continue;
    if (add_worker_move_to_target(S, M, P, a, planned_gold, target, true)) {
      ++workers_sent;
    }
  }
  if (workers_sent > 0) {
    if (planned_bases >= 2)
      add_train_if_needed(S, M, a, planned_gold, 1);
    return a;
  }

  if (turn >= 35 && minimum_staff_deficit(S, a, M) > 0 &&
      add_critical_worker_fill_moves(S, M, P, a, planned_gold)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (hq->level == 1 && current_my_bases >= 4 && turn >= 55 &&
      !waiting_initial_build && !used_upgrades.count(hq->region)) {
    if (planned_gold < HQ_LEVELS[2].upgrade_cost && turn < 120)
      return a;
    if (planned_gold >= HQ_LEVELS[2].upgrade_cost &&
        add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                             hq->region)) {
      add_train_if_needed(S, M, a, planned_gold, 1);
      return a;
    }
  }

  if (hq->level == 2 && !waiting_initial_build &&
      !used_upgrades.count(hq->region) &&
      allow_favorable_hq3_pressure(S, M, P, a, planned_gold, turn,
                                   current_my_bases)) {
    if (add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                             hq->region)) {
      add_train_if_needed(S, M, a, planned_gold,
                          HQ_LEVELS[hq->level].train_cap);
      return a;
    }
  }

  if (add_hq_upgrade_when_enemy_bases_low(S, M, P, a, used_upgrades,
                                          planned_gold, turn, hq)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (add_low_enemy_base_hq_pressure(S, M, P, a, planned_gold, turn)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (add_late_direct_hq_pressure(S, M, P, a, planned_gold, turn)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (turn >= 195 &&
      add_sub90_warm_hq_finish(S, M, P, a, planned_gold, turn,
                               warm_capture_regions)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  bool staged_finish_ready =
      turn >= 120 &&
      (count_forward_my_bases(S, M, P) > 0 || current_my_bases >= 4 ||
       count_enemy_bases(S, M) <= 4);
  if (turn >= 135 && staged_finish_ready &&
      add_sub90_warm_staged_hq_finish(S, M, P, a, planned_gold, turn)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  bool capture_ready =
      current_my_bases >= 2 && (count_my_alive(S, M) >= 10 || turn >= 45);
  int capture_need_for_training = 0;
  if (capture_ready) {
    if (count_enemy_bases(S, M) <= 0)
      warm_capture_failed_targets.clear();
    if (sub90_all_enemy_bases_failed(S, M, warm_capture_failed_targets)) {
      warm_capture_failed_targets.clear();
      warm_capture_target = -1;
      if (a.train_n == 0)
        add_train_if_needed(S, M, a, planned_gold,
                            HQ_LEVELS[hq->level].train_cap);
      return a;
    }

    int capture_attempts = std::max(1, count_enemy_bases(S, M));
    while (capture_attempts-- > 0) {
      bool keep_warm_target = false;
      if (sub90_valid_enemy_base_target(S, M, P, warm_capture_target)) {
        int current_stage =
            sub90_shortest_path_predecessor(P, M.my_hq, warm_capture_target);
        keep_warm_target = current_stage >= 0 &&
                           sub90_any_moving_to_region(S, M, current_stage);
      }
      if (!keep_warm_target) {
        warm_capture_target = select_warm_capture_target_excluding(
            S, M, P, warm_capture_target, turn, warm_capture_failed_targets);
      }
      if (warm_capture_target < 0)
        break;
      warm_capture_regions.insert(warm_capture_target);
      int need = warm_capture_attack_need(S, M, P, warm_capture_target, turn);
      capture_need_for_training = need;

      int available = count_my_alive(S, M) -
                      planned_moves_from_region(a, S, M.my_hq);
      if (available < need && !sub90_target_base_damaged(S, M, warm_capture_target)) {
        if (a.train_n == 0)
          add_train_if_needed(S, M, a, planned_gold,
                              HQ_LEVELS[hq->level].train_cap);
        return a;
      }

      if (add_forward_capture_moves(S, M, P, a, planned_gold,
                                    warm_capture_target, need,
                                    warm_capture_regions)) {
        add_train_if_needed(S, M, a, planned_gold,
                            HQ_LEVELS[hq->level].train_cap);
        return a;
      }

      break;
    }
  }

  if (staged_finish_ready &&
      add_sub90_warm_staged_hq_finish(S, M, P, a, planned_gold, turn)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (turn >= 178 &&
      add_sub90_warm_hq_finish(S, M, P, a, planned_gold, turn,
                               warm_capture_regions)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (hq->level == 1 && current_my_bases >= 2 && turn >= 62 &&
      !waiting_initial_build && count_enemy_bases(S, M) > 0 &&
      !used_upgrades.count(hq->region)) {
    if (planned_gold < HQ_LEVELS[2].upgrade_cost && turn < 120)
      return a;
    if (planned_gold >= HQ_LEVELS[2].upgrade_cost)
      add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
  }

  if (!a.upgrades.empty()) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  if (turn >= 70 && total_worker_deficit(S, a, M) > 0 &&
      add_worker_fill_moves(S, M, P, a, planned_gold)) {
    add_train_if_needed(S, M, a, planned_gold,
                        HQ_LEVELS[hq->level].train_cap);
    return a;
  }

  int desired_alive = hq->work_cap() + std::max(2, current_my_bases) +
                      std::max(10, capture_need_for_training + 8);
  if (turn >= 110)
    desired_alive += 8;
  if (turn >= 135)
    desired_alive += 8;
  int want_train = std::max(0, desired_alive - count_my_alive(S, M));
  int reserve_gold = waiting_initial_build ? BASE_LEVELS[1].cost : 0;
  int train_gold = std::max(0, planned_gold - reserve_gold);
  add_train_if_needed(S, M, a, train_gold,
                      std::min(HQ_LEVELS[hq->level].train_cap,
                               std::max(1, want_train)));
  if (a.train_n > 0)
    planned_gold -= a.train_n * TRAIN_COST;

  if (a.train_n == 0) {
    int train_all_gold = std::max(0, planned_gold - reserve_gold);
    add_train_if_needed(S, M, a, train_all_gold,
                        affordable_train_count(
                            train_all_gold, HQ_LEVELS[hq->level].train_cap));
    if (a.train_n > 0)
      planned_gold -= a.train_n * TRAIN_COST;
  }

  add_optional_rebuild_lost_bases(S, M, a, used_upgrades, planned_gold,
                                  planned_bases, ever_owned_base_regions);
  return a;
}

static Actions decide_small_attack(const GameState &S, const GameMap &M, const Paths &P,
                      int turn) {
  Actions a;
  std::set<int> used_upgrades;
  int planned_gold = std::max(0, S.gold);

  const Building *hq = my_hq_building(S, M);
  if (hq == nullptr)
    return a;

  static int forward_capture_target = -1;
  static std::set<int> forward_capture_regions;
  static int max_my_bases_seen = 0;
  static std::set<int> ever_owned_base_regions;
  static int low_base_recovery_target = -1;
  if (turn <= 1) {
    forward_capture_target = -1;
    forward_capture_regions.clear();
    max_my_bases_seen = 0;
    ever_owned_base_regions.clear();
    low_base_recovery_target = -1;
  }

  int current_my_bases = count_my_bases(S, M);
  max_my_bases_seen = std::max(max_my_bases_seen, current_my_bases);
  for (const auto &b : S.buildings) {
    if (b.side == M.my_side && b.type == BType::BASE)
      ever_owned_base_regions.insert(b.region);
  }

  int planned_bases = current_my_bases;
  int target_bases = count_target_bases_built(S, M, P);
  std::vector<int> targets = log2_target_order(S, M, P);
  int active_target_goal =
      std::min(TARGET_BASE_COUNT, static_cast<int>(targets.size()));
  int hq2_base_gate = std::min(6, active_target_goal);
  int hq3_level2_gate = std::min(5, active_target_goal);
  int hq4_level2_gate = std::min(9, active_target_goal);
  int hq5_level2_gate = active_target_goal;
  int preupgrade_target = next_level1_upgrade_target_region(S, M, P);
  int aggressive_base_goal = std::min(active_target_goal, 6);
  bool a_style_attack_mode =
      current_my_bases >= 3 || target_bases >= 3 || turn >= 35;
  auto allow_small_map_score_upgrade = [&](int next_level) {
    if (M.N > 56 || !a_style_attack_mode || current_my_bases < 3)
      return false;
    if (next_level == 3)
      return turn >= 55;
    if (next_level == 4)
      return turn >= 95;
    if (next_level == 5)
      return turn >= 135;
    return false;
  };

  prime_hq_assault_rally_lock(S, M, P, a, turn);
  if (add_forced_hq_race_launch_if_ready(S, M, P, a, planned_gold, turn))
    return a;
  if (add_small_forced_hq_race_launch_if_ready(S, M, P, a, planned_gold,
                                               turn))
    return a;

  bool enemy_inside_hq = count_enemy_warriors_at(S, M.my_hq, M) > 0;
  if (enemy_inside_hq) {
    add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
    if (turn < 40) {
      add_train_if_needed(S, M, a, planned_gold, hq->level < 5 ? 1 : 3);
      return a;
    }
    for (const auto &w : S.warriors) {
      if (w.id.side != M.my_side || w.state != WState::STATIONARY)
        continue;
      if (!should_recall_for_emergency(w, M))
        continue;
      if (w.region == M.my_hq || warrior_already_planned(a, w.id))
        continue;
      if (P.nxt[w.region][M.my_hq] == -1)
        continue;
      int cost = move_cost_to(S, M, M.my_hq);
      if (planned_gold < cost)
        break;
      a.moves.emplace_back(w.id, M.my_hq);
      planned_gold -= cost;
    }
    add_front_half_hq_pressure_under_emergency(S, M, P, a, planned_gold);
    add_train_if_needed(S, M, a, planned_gold, hq->level < 5 ? 1 : 3);
    return a;
  }

  if (apply_small_map_hq_approach_defense(S, M, P, a, used_upgrades,
                                           planned_gold, hq)) {
    return a;
  }

  if (M.N <= 56 && turn >= 70 && total_worker_deficit(S, a, M) > 0 &&
      add_worker_fill_moves(S, M, P, a, planned_gold)) {
    return a;
  }

  add_forward_base_builds(S, M, a, used_upgrades, planned_gold, planned_bases,
                          forward_capture_regions);

  if (turn >= 150 && total_worker_deficit(S, a, M) > 0 &&
      add_worker_fill_moves(S, M, P, a, planned_gold)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (add_late_split_capture_if_favorable(
          S, M, P, a, planned_gold, turn, forward_capture_target,
          forward_capture_regions)) {
    int cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    if (a.train_n == 0)
      add_train_if_needed(S, M, a, planned_gold,
                          affordable_train_count(planned_gold, cap));
    return a;
  }

  if (add_decisive_hq_push_if_ready(S, M, P, a, planned_gold, turn))
    return a;

  if (add_late_total_all_in_moves(S, M, P, a, planned_gold, turn))
    return a;

  add_captured_base_fill_moves(S, M, P, a, planned_gold,
                               forward_capture_regions);
  int capture_staff_deficit =
      captured_base_worker_deficit(S, M, a, forward_capture_regions);

  if (hq->level < HQ_MAX_LEVEL && !used_upgrades.count(hq->region)) {
    int next_level = hq->level + 1;
    int target_level2 = count_target_level2_bases(S, M, P);
    bool allow_hq = false;
    if (next_level == 2) {
      allow_hq = target_bases >= hq2_base_gate;
    } else if (next_level == 3) {
      allow_hq = target_level2 >= hq3_level2_gate || turn >= 89;
    } else if (next_level == 4) {
      allow_hq = target_level2 >= hq4_level2_gate || turn >= 127;
    } else if (next_level == 5) {
      allow_hq = target_level2 >= hq5_level2_gate ||
                 (target_level2 >= core_level2_goal(active_target_goal) &&
                 count_forward_my_bases(S, M, P) > 0) ||
                 turn >= 140;
    }
    if (allow_small_map_score_upgrade(next_level))
      allow_hq = true;
    else if (a_style_attack_mode && next_level >= 3)
      allow_hq = false;
    if (allow_hq &&
        !add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold,
                              hq->region)) {
      add_target_base_fill_moves(S, M, P, a, planned_gold, 4,
                                 preupgrade_target);
      return a;
    }
  }

  for (int target : targets) {
    if (planned_bases >= TARGET_BASE_COUNT)
      break;
    if (enemy_building_at(S, M, target) || is_my_base_at(S, M, target))
      continue;
    if (count_my_warriors_at(S, target, M) == 0 ||
        count_enemy_warriors_at(S, target, M) > 0) {
      continue;
    }
    add_base_build(S, M, a, used_upgrades, planned_gold, planned_bases,
                   target);
  }

  int target_level2 = count_target_level2_bases(S, M, P);
  if (hq->level < HQ_MAX_LEVEL && !used_upgrades.count(hq->region)) {
    int next_level = hq->level + 1;
    bool allow_hq = false;
    if (next_level == 2) {
      allow_hq = target_bases >= hq2_base_gate;
    } else if (next_level == 3) {
      allow_hq = target_level2 >= hq3_level2_gate || turn >= 89;
    } else if (next_level == 4) {
      allow_hq = target_level2 >= hq4_level2_gate || turn >= 127;
    } else if (next_level == 5) {
      allow_hq = target_level2 >= hq5_level2_gate ||
                 (target_level2 >= core_level2_goal(active_target_goal) &&
                 count_forward_my_bases(S, M, P) > 0) ||
                 turn >= 140;
    }
    if (allow_small_map_score_upgrade(next_level))
      allow_hq = true;
    else if (a_style_attack_mode && next_level >= 3)
      allow_hq = false;
    if (allow_hq)
      add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
  }

  bool capture_phase_ready =
      (a_style_attack_mode ||
       (!has_open_neutral_target(S, M, P) ||
        target_bases >= active_target_goal || turn >= 95)) &&
      (target_bases >= 3 || current_my_bases >= 3 || turn >= 35);
  int capture_need_for_training = 0;
  if (capture_phase_ready && capture_staff_deficit == 0) {
    forward_capture_target =
        select_forward_capture_target(S, M, P, forward_capture_target);
    if (forward_capture_target != -1) {
      forward_capture_regions.insert(forward_capture_target);
      int need = capture_attack_need(S, M, P, forward_capture_target);
      capture_need_for_training = need;
      add_forward_capture_moves(S, M, P, a, planned_gold,
                                forward_capture_target, need,
                                forward_capture_regions);
    }
  }

  if (!a_style_attack_mode) {
    for (int target : targets) {
      const Building *b = find_building(S, target);
      if (b == nullptr || b->side != M.my_side || b->type != BType::BASE ||
          b->level >= 2) {
        continue;
      }
      if (build_phase_stationary_count_at(S, a, target, M) < 2)
        continue;
      add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, target);
    }
  }

  int planned_target_level2 = target_level2;
  for (int region : a.upgrades) {
    const Building *b = find_building(S, region);
    if (b != nullptr && b->side == M.my_side && b->type == BType::BASE &&
        b->level == 1) {
      ++planned_target_level2;
    }
  }

  if (hq->level < HQ_MAX_LEVEL && !used_upgrades.count(hq->region)) {
    int next_level = hq->level + 1;
    bool allow_hq = false;
    if (next_level == 2) {
      allow_hq = target_bases >= hq2_base_gate;
    } else if (next_level == 3) {
      allow_hq = planned_target_level2 >= hq3_level2_gate || turn >= 89;
    } else if (next_level == 4) {
      allow_hq = planned_target_level2 >= hq4_level2_gate || turn >= 127;
    } else if (next_level == 5) {
      allow_hq = planned_target_level2 >= hq5_level2_gate ||
                 (planned_target_level2 >= core_level2_goal(active_target_goal) &&
                 count_forward_my_bases(S, M, P) > 0) ||
                 turn >= 140;
    }
    if (allow_small_map_score_upgrade(next_level))
      allow_hq = true;
    else if (a_style_attack_mode && next_level >= 3)
      allow_hq = false;
    if (allow_hq)
      add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, hq->region);
  }

  bool macro_complete = target_macro_complete(S, a, M, P);
  if (!macro_complete) {
    add_target_base_fill_moves(S, M, P, a, planned_gold, 4,
                               preupgrade_target);

    int issued_workers = 0;
    for (int target : targets) {
      if (issued_workers >= 3)
        break;
      if (enemy_building_at(S, M, target) || is_my_base_at(S, M, target))
        continue;
      if (has_worker_or_pending_for_target(S, M, target))
        continue;
      if (add_worker_move_to_target(S, M, P, a, planned_gold, target, true,
                                    preupgrade_target, 2))
        ++issued_workers;
    }

    add_excess_base_moves_to_hq(S, M, P, a, planned_gold, 4,
                                preupgrade_target, 2);

    int desired_alive = 1 + aggressive_base_goal + hq->work_cap();
    desired_alive += capture_need_for_training;
    desired_alive += capture_staff_deficit;
    desired_alive += a_style_attack_mode ? 12 : 4;
    if (hq->level >= HQ_MAX_LEVEL)
      desired_alive += 8;
    int train_cap = hq->level >= HQ_MAX_LEVEL ? HQ_LEVELS[hq->level].train_cap : 1;
    int current_after_train = count_my_alive(S, M) + a.train_n;
    int want_train = std::max(0, desired_alive - current_after_train);

    bool build_waiting = false;
    for (int target : targets) {
      if (!is_my_base_at(S, M, target) && !enemy_building_at(S, M, target) &&
          count_my_warriors_at(S, target, M) > 0 &&
          count_enemy_warriors_at(S, target, M) == 0) {
        build_waiting = true;
      }
    }

    int reserve_gold = 0;
    if (M.N <= 56 && hq->level == 4 && turn >= 155)
      reserve_gold += HQ_LEVELS[5].upgrade_cost;
    if (build_waiting)
      reserve_gold += BASE_LEVELS[1].cost;
    int pending_build_sites = 0;
    for (int target : targets) {
      if (used_upgrades.count(target))
        continue;
      if (is_my_base_at(S, M, target) || enemy_building_at(S, M, target))
        continue;
      bool pending_worker = has_worker_heading_to(S, M, target) ||
                            planned_moves_to_region(a, target) > 0 ||
                            count_my_warriors_at(S, target, M) > 0;
      if (pending_worker)
        ++pending_build_sites;
    }
    reserve_gold += BASE_LEVELS[1].cost * pending_build_sites;
    if (!a_style_attack_mode &&
        count_target_bases_built(S, M, P) >= active_target_goal &&
        count_target_level2_bases(S, M, P) < active_target_goal) {
      reserve_gold += BASE_LEVELS[2].cost;
    }

    int train_gold = std::max(0, planned_gold - reserve_gold);
    if (want_train > 0 && train_gold >= TRAIN_COST) {
      int train_plan_gold = train_gold;
      add_train_if_needed(S, M, a, train_plan_gold,
                          std::min(train_cap, want_train));
      if (a.train_n > 0)
        planned_gold -= a.train_n * TRAIN_COST;
    }

    if (a.train_n == 0 && hq->level >= HQ_MAX_LEVEL &&
        train_gold >= TRAIN_COST) {
      int train_plan_gold = train_gold;
      add_train_if_needed(S, M, a, train_plan_gold,
                          affordable_train_count(
                              train_gold, HQ_LEVELS[hq->level].train_cap));
      if (a.train_n > 0)
        planned_gold -= a.train_n * TRAIN_COST;
    }
    add_optional_rebuild_lost_bases(S, M, a, used_upgrades, planned_gold,
                                    planned_bases, ever_owned_base_regions);
    return a;
  }

  if (!a_style_attack_mode) {
    for (int target : targets) {
      const Building *b = find_building(S, target);
      if (b == nullptr || b->side != M.my_side || b->type != BType::BASE ||
          b->level != 1) {
        continue;
      }
      if (build_phase_stationary_count_at(S, a, target, M) < 2)
        continue;
      if (add_upgrade_if_legal(S, M, a, used_upgrades, planned_gold, target))
        return a;
    }

    for (int target : targets) {
      const Building *b = find_building(S, target);
      if (b == nullptr || b->side != M.my_side || b->type != BType::BASE ||
          b->level != 1) {
        continue;
      }
      if (committed_my_count_at(S, a, target, M) >= 2)
        continue;
      if (add_surplus_moves_to_region(S, M, P, a, planned_gold, target, 1))
        return a;
    }
  }

  const Building *rally = my_hq_building(S, M);
  if (add_rally_attack_if_ready(S, M, P, a, planned_gold, rally))
    return a;

  add_worker_fill_moves(S, M, P, a, planned_gold);
  add_rally_gather_moves(S, M, P, a, planned_gold, rally);

  int cap = HQ_LEVELS[hq->level].train_cap;
  int wanted = std::max(total_worker_deficit(S, a, M),
                        RALLY_ATTACK_COUNT -
                            (rally == nullptr
                                 ? 0
                                 : effective_my_count_at(S, a,
                                                         rally->region, M)));
  add_train_if_needed(S, M, a, planned_gold,
                      std::min(cap, std::max(0, wanted)));
  if (a.train_n == 0) {
    add_train_if_needed(S, M, a, planned_gold,
                        affordable_train_count(planned_gold, cap));
  }
  add_optional_rebuild_lost_bases(S, M, a, used_upgrades, planned_gold,
                                  planned_bases, ever_owned_base_regions);
  return a;
}

static void trim_large_early_small_enemy_base_attack_batches(
    const GameState &S, const GameMap &M, int turn, Actions &a) {
  if (!large_strategy_active(M) || turn >= 130)
    return;
  std::map<int, int> direct_enemy_base_moves;
  for (const auto &move_plan : a.moves) {
    const Building *dst = find_building(S, move_plan.second);
    if (dst != nullptr && dst->side != M.my_side && dst->type == BType::BASE)
      ++direct_enemy_base_moves[move_plan.second];
  }
  if (direct_enemy_base_moves.empty())
    return;

  std::vector<std::pair<WarriorId, int>> kept;
  kept.reserve(a.moves.size());
  for (const auto &move_plan : a.moves) {
    const Building *dst = find_building(S, move_plan.second);
    bool early_small_attack =
        dst != nullptr && dst->side != M.my_side && dst->type == BType::BASE &&
        direct_enemy_base_moves[move_plan.second] < 3;
    if (early_small_attack) {
      large_goal_clear(move_plan.first);
      continue;
    }
    kept.push_back(move_plan);
  }
  a.moves.swap(kept);
}

static Actions decide(const GameState &S, const GameMap &M, const Paths &P,
                      int turn) {
  update_idle_base_surplus_turns(S, M);
  Actions a = FORCE_WARM_STRATEGY_ALL_MAPS
                  ? decide_sub90_warm_table(S, M, P, turn)
                  : (M.N >= 90) ? decide_large_recovery(S, M, P, turn)
                                : decide_sub90_warm_table(S, M, P, turn);
  int planned_gold = remaining_gold_after_actions(S, M, a);
  bool drained = false;
  if (large_strategy_active(M)) {
    drained =
        add_idle_base_surplus_drain_moves(S, M, P, a, planned_gold, turn);
    while (turn >= 90 && a.train_n > 0) {
      int retry_gold = planned_gold + TRAIN_COST;
      --a.train_n;
      if (add_idle_base_surplus_drain_moves(S, M, P, a, retry_gold, turn)) {
        planned_gold = retry_gold;
        drained = true;
        continue;
      }
      ++a.train_n;
      break;
    }
  }
  (void)drained;
  if (large_strategy_active(M))
    trim_large_early_small_enemy_base_attack_batches(S, M, turn, a);
  trim_final_turn_unusable_train(S, M, a, turn, a.train_n);
  return a;
}
int main() {
  GameMap M;
  GameState S;
  parse_init(M, S);
  Paths P = calculate_paths(M);

  int turn;
  while (read_turn_start(turn)) {
    Actions a = decide(S, M, P, turn);
    emit_command();
    emit_actions(a);
    emit_end();
    read_turn_result(S, M, a);
  }
  return 0;
}

