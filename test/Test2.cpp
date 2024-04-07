#include "Test2.h"



struct StateTest2Main {
  int mark;
  int fresh;
  int tag;
  union {
    struct {
      int begin;
    } FanOn;
  } params;
};

struct MemoryTest2MainFanOff {
  int init;
};

struct MemoryTest2MainFanOn {
  int init;
};

struct MemoryTest2MainFanSleep {
  int init;
  int timer[2];
};

struct MemoryTest2Main {
  int init;
  int clock[2];
  double di[2];
  int ctime[2];
  int otime[2];
  int fan[2];
  struct StateTest2Main* state;
  union {
    struct MemoryTest2MainFanOff FanOff;
    struct MemoryTest2MainFanOn FanOn;
    struct MemoryTest2MainFanSleep FanSleep;
  } statebody;
};

int clock;
int period = 9;
int current_side;

struct StateTest2Main memory_StateTest2Main[2];
int size_StateTest2Main = 2;
int counter_StateTest2Main = 0;
