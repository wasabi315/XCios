#include "Test1.h"



struct MemoryTest1Main {
  int init;
  double tmp[2];
  double hmd[2];
  double di[2];
  int fan[2];
  double ho[2];
};

int clock;
int period = 7;
int current_side;

struct MemoryTest1Main memory;

static void header_init_Test1Main_fan(struct MemoryTest1Main*);
static void update_Test1Main_di(struct MemoryTest1Main*);
static void update_Test1Main_fan(struct MemoryTest1Main*);
static void update_Test1Main_ho(struct MemoryTest1Main*);
static void update_Test1Main(struct MemoryTest1Main*);
static void free_Test1Main(struct MemoryTest1Main*);
static void refresh_mark();
extern void input(double*, double*);
extern void output(double*, int*);

static void header_init_Test1Main_fan(struct MemoryTest1Main* memory) {
  memory->fan[!current_side] = 0;
}

static void update_Test1Main_di(struct MemoryTest1Main* memory) {
  memory->di[current_side] =
    (((0.81 * memory->tmp[current_side]) + ((0.01 * memory->hmd[current_side]) * ((0.99 * memory->tmp[current_side]) - 14.3))) + 46.3);
}

static void update_Test1Main_fan(struct MemoryTest1Main* memory) {
  memory->fan[current_side] =
    (memory->di[current_side] >= (-75. + memory->ho[current_side]));
}

static void update_Test1Main_ho(struct MemoryTest1Main* memory) {
  double _tmpvar1;
  if (memory->fan[!current_side]) {
    _tmpvar1 = 0.5;
  } else {
    _tmpvar1 = 0.5;
  }
  memory->ho[current_side] = _tmpvar1;
}

static void update_Test1Main(struct MemoryTest1Main* memory) {
  int entry = clock;
  if (memory->init) {
    header_init_Test1Main_fan(memory);
  }
  clock = entry + 1;
  clock = entry + 2;
  update_Test1Main_ho(memory);
  clock = entry + 3;
  update_Test1Main_di(memory);
  clock = entry + 4;
  update_Test1Main_fan(memory);
  clock = entry + 5;
  memory->init = 0;
}

static void free_Test1Main(struct MemoryTest1Main* memory) {
  if (memory->init) return;
  memory->init = 1;
}

static void refresh_mark() {
  int i;
}

void activate() {
  current_side = 0;
  clock = 0;
  memory.init = 1;
  while (1) {
    clock = 0;
    clock = 1;
    input(&memory.tmp[current_side], &memory.hmd[current_side]);
    update_Test1Main(&memory);
    output(&memory.di[current_side], &memory.fan[current_side]);
    clock = period;
    refresh_mark();
    current_side = !current_side;
  }
}
