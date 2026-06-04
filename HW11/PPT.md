# Week 13 编译 (H) COMP130014h.01

## 本周内容

- Instructions Selection 指令选择
  - 输入：SSA Quad
  - 输出：ARMv7-A 程序 (只使用一个小的子集)
- 关键步骤:
  1. 对每一个 basic block 建立一个 advDFG (Advanced Data Flow Graph)
  2. 每一个 basic block 内部进行指令选择形成 preschedule
  3. 理解 ARM 的 function call 的实现机理 (Activation Record)
  4. 将 pre Schedule 进行线性化处理 (function call,phi function 等) 形成 ARM 汇编程序
- 现阶段限制：register 还是基本使用 temp (unlimited supply)

## ARM Instructions for FDMJ

- 课程仅选用一小部分 ARMv7-A 指令子集；精简指令有利于生成优化代码

### ARM 整型指令分类

#### 1. Arithmetic instructions 算术指令

表格

|          Instruction           |           Meaning           |
| :----------------------------: | :-------------------------: |
|    add destReg, srcReg, op2    |   destReg = srcReg + op2    |
|    sub destReg, srcReg, op2    |   destReg = srcReg - op2    |
|    rsb destReg, srcReg, op2    |   destReg = op2 - srcReg    |
| mul destReg, srcReg1, srcReg2  | destReg = srcReg1 * srcReg2 |
| sdiv destReg, srcReg1, srcReg2 | destReg = srcReg1 / srcReg2 |

> Notes
>
> 1. 所有有符号运算基于 32 位二进制补码
> 2. `rsb`可用于取反：`rsb r0, r0, #0`等价`neg r0,r0`
> 3. op2 可选：通用寄存器 /imm8m 立即数 / 带移位操作的寄存器 (如`r0, ASL #1`等价 r0*2)

#### 2. Move & Memory Instructions 传送与访存指令

表格

|             Instruction              |                Meaning                 |
| :----------------------------------: | :------------------------------------: |
|           mov destReg, op2           |             destReg = op2              |
|         movw destReg, imm16          | destReg 低 16 位 = imm16 (16 位立即数) |
|         movt destReg, imm16          |        destReg 高 16 位 = imm16        |
| ldr destReg, [locationReg[, offset]] |         destReg = 内存地址内容         |
|        ldr destReg, =<label>         |        destReg = label 对应常量        |
|          adr destReg, label          |   destReg = label 地址 (仅局部标签)    |
| str srcReg, [locationReg[, offset]]  |           内存地址 = srcReg            |

> 补充说明
>
> 1. `movw+movt`组合可加载任意 32 位常数到寄存器
> 2. offset 可选立即数 / 寄存器，示例：`ldr r0,[r1]`/`ldr r0,[r1,#12]`/`ldr r0,[r1,r2]`
> 3. 不存在`str xx,=label`语法

#### 3. Compare and Branch 比较跳转指令

表格

|  Instruction  |            Meaning             |
| :-----------: | :----------------------------: |
| cmp Reg1, op2 | Reg1-op2，状态写入 CPSR 寄存器 |
|    b label    |         无条件直接跳转         |
|   bl label    |     跳转 + 返回地址存入 lr     |
|  bx register  |      跳转到寄存器存储地址      |
| blx register  |      bx + 返回地址存入 lr      |

> Notes
>
> 1. 指令可追加条件后缀 (依据 CPSR)：`eq/ne/ge/gt/le/lt`
> 2. 示例：`bxne r3`、`addeq r0,r0,r0`、`bgt fun`

## Activation Records 活动记录 (栈帧)

### 函数调用与返回原理

1. 函数局部变量 / 形参在函数调用时创建，每次调用拥有独立副本，函数退出后生命周期结束
2. 高阶函数 / 嵌套函数场景局部变量生命周期延长，**FDMJ/C 无此场景**

### 变量需要存入内存 (逃逸 escape) 的条件

- 变量被取地址 (&)、被嵌套函数访问、数据尺寸超单寄存器、数组、寄存器资源不足溢出 (spill)

> FDMJ 所有数据均可存入寄存器，默认无变量逃逸

### ARM AAPCS 调用规范

#### 寄存器划分

表格

|            分类             |                            寄存器                            |                       规则                        |
| :-------------------------: | :----------------------------------------------------------: | :-----------------------------------------------: |
|  caller-saved (调用方保存)  |                        r0~r3、lr、pc                         | 调用函数后内容可能被篡改；r0~r3 传参，r0 存返回值 |
| callee-saved (被调用方保存) |                        r4~r11、sp、fp                        |      被调用函数修改前需入栈保存，返回前恢复       |
|            特殊             | sp (r13) 栈指针、fp (r11) 帧指针、lr (r14) 链接寄存器、pc (r15) 程序计数器 |                         -                         |

#### 参数传递规则

1. ARM 最多用 r0~r3 四个寄存器传参，超出参数压栈
2. 即使参数≤4 个，栈帧通常仍预留对应栈空间 (适配可变参如 printf)
3. FDMJ 无逃逸变量，仅在寄存器不足时才将变量存入栈帧

### FDMJ 栈帧布局

> 栈由高地址向低地址增长
>
> 栈帧组成：保存的被调用寄存器区 → 入参区 → 出参区 → 局部临时变量区 → 静态链 → 返回地址

### 函数汇编示例

asm

```
# main函数开头
.global __$main__
$main__^main:
L100: push {r4-r10, fp, lr}
sub sp,sp,#4
add fp, sp, #36
...
# max函数标准序言
.global C^max
C^max:
L105: push {r4-r10, fp, lr}
sub sp,sp,#4
add fp, sp, #36
```

## ARM 高级指令选择 (基于 SSA 四元式)

### CFG & advDFG 构建 (每个函数)

1. **控制边 (红边)**：访存 / 函数调用语句有先后顺序则添加控制流边，用 token 标记先后依赖
2. **数据流边 (绿边)**：s1 定义临时变量、s2 使用该变量，s1→s2 连边；常量抽为独立节点
3. **Live-out 边 (紫边)**：函数出口存活临时变量与块尾语句连边

### 单个基本块指令选择

- 贪心 + 分块 (Tiling) 算法：自上而下遍历数据流图，找到匹配指令模板后生成汇编，存入`preSchedule`
- preSchedule 保存：块入口标签、Phi 结点、生成指令、块尾指令

### 全局线性化 Schedule

1. 按函数块 CFG 顺序遍历，处理 CJUMP / 无条件 JUMP 与 Phi 函数
2. Phi 替换：跳转前补充 move 指令完成 Phi 赋值
   - 条件跳转：False 分支 fallthrough，True 分支末尾补充 b 跳转
   - 无条件跳转：直接跳转至目标块，节省跳转指令
3. 最终拼接所有块指令，生成完整 ARM 汇编