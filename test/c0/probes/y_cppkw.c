#include "c0.h"
//T class u32 : u32 : 1
u32 class(u32 new) { u32 delete = new + 1u; u32 this = delete * 2u; return this; }
//T template u32 : u32 : 1
u32 template(u32 x) { return class(x) + 1u; }
