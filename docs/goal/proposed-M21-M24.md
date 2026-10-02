# M21–M24 提案：核对结果与任务板行

这份文档对应任务板 `docs/goal/task-board.yaml` 里新加的 43 行（M21–M24）。其中 2 行已完成（`DONE_STRONG`，证据见
`docs/goal/evidence/M21-QBF-ARITH.md`），其余为 `TODO_READY` 或 `TODO_NEEDS_DESIGN`。
排名接在 M20 之后（1600 起），**没有改动现有队列的顺序**，`active_milestone` 仍是 M14。要提前做 M21，改 rank 即可。

## 一、对原清单的核对（按仓库实际内容）

逐条对照了 `Start/` 下的全部模块。下面几处和原清单不一致，建议在对外表述中改正。

### 1. IP = PSPACE 的前置并没有"全铺齐"

- **`TQBF ∈ PSPACE` 没有证明。** 已证明的只有 PSPACE-困难性（`Complexity.Qbf.QBF.pspaceHard_tqbfLang`）。
  成员性仍是开放任务 `M14-TQBF-IN-PSPACE`，卡在 `M14-QBF-STEP-PROG`（单步带程序）上。所以 TQBF 目前是
  "困难"，不是"完全"。
- **`QbfCob*` 不是算术化。** `Cob` 指 Cobham 类：这 14 个模块是 PSPACE-困难性归约的多项式时间编译器，
  用多项式时间的字操作写出归约公式，和多项式、有限域都无关。算术化本身这次从零写起（见下文 `Start/QbfArith.lean`）。
- **`IP ⊆ PSPACE` 被一个更基础的缺口卡住：库里连 `P ⊆ PSPACE` 都没有。** 原因是时间在 Cobham 类上度量，
  空间在离线机上度量，而两者之间没有编译器。这个缺口已经写在 `M15-ORACLE-CLASSES` 和 `M15-BGS-EQUAL` 的
  `open_boundary` 里。所以 IP = PSPACE 这一方向要先做 `M21-COBHAM-TO-SPACE`，它同时也会解开 M15 那两行。
- **`PSPACE ⊆ IP` 这一方向确实可行，且不依赖上面两个缺口。** 它只需要困难性（已有）、IP 对多项式时间归约封闭，
  以及 TQBF 的 sum-check 协议，验证者是 Cobham 项。
- 还缺一个技术点：**度数约减**（Shen 的线性化算子）。没有它，每个量词都可能让度数翻倍，验证者也就不是多项式时间的。
  已单列为 `M21-LINEARIZE`。
- 一个对工程有利的事实（已在 Lean 中证明）：算术化在 0/1 输入上的值**恰好**是 0 或 1，在任何交换环里都成立
  （`tqbf_iff_arith`）。因此对素数 p 没有额外条件：取一个多项式大小的素数（O(log n) 位），验证者自己用试除法就能找到，
  不需要 Pratt 证书。

### 2. λΠ 的类型检查算法已经有了

`Start/LambdaPiInfer.lean` 已经实现了双向类型推断，结果按构造即正确（返回类型连同推导），另外证明了完备性，
并给出 `LambdaPi.decidableTypable` / `LambdaPi.decidableTyping`（可判定性）。转换的可判定性在 `Start/LambdaPiNormalize.lean`。
库里缺的只是 NbE 这一种具体算法，不是"类型检查的可判定性"。因此没有为它开行。

### 3. 其他前置上的出入

- **序数：库里零命中。** System T 有，序数没有（Mathlib 有 `Ordinal` 和 `ONote`）。所以 Gentzen 和证明论式的逆数学并不像
  原清单说的"前置都有"。逆数学我改走 ω-模型路线（`M24-OMEGA-MODELS`），用库里已有的 Turing 归约和跳跃，不需要序数。
- **形式算术理论：没有。** `ChaitinIncompleteness` 用的是抽象的"可靠、递归可枚举的证明系统"，库里没有 PA 的语法和
  证明谓词。Gödel II 因此拆成两步：先做抽象的 Löb（把可导性条件 D1–D3 作为假设，篇幅小），再做 PA 本身
  （`M24-ARITH-THEORY` → `M24-GODEL2-ARITH`，其中 D3，即内部 Σ₁-完备性，是最贵的一步）。
- **恒等类型：没有。** λΠ 的项只有 `var/sort/app/lam/pi`，System F 也没有 Id。groupoid 模型能反驳 UIP，前提是先有
  Id 类型的结构。已单列为 `M23-ID-TYPES`（CwA 上的 Id 结构），它是真前置，不是走形式。`UIP` 的 4 处命中都是别的单词的子串，
  不是恒等类型。
- **非确定带程序：没有。** `Complexity.Space.Prog` 只编译成确定机器。Immerman–Szelepcsényi 和空间层级定理都卡在
  "单步层写带程序"这一层，与 TQBF ∈ PSPACE 是同一个瓶颈。已单列为 `M22-NONDET-PROG`。
- **coNP：零命中。** Cook–Reckhow 需要先定义它，见 `M22-CONP-PH`。
- **时间层级定理：** 已有一行 `M15-TIME-HIERARCHY-REL`（相对化版本，`TODO_READY`），没有重复开行。

### 4. 关于"全世界还没人形式化过"

我无法可靠地核实"从未形式化"这类全称断言，建议对外不要这么写。有几条据我所知已经有人做过：

- **Gödel 第二不完备性：** 有 Paulson 在 Isabelle 中的形式化；Lean 社区的 Foundation 项目据我所知也有，包括 GL。
- **Hurkens 悖论：** Coq 标准库里有（`Coq.Logic.Hurkens`）。
- **CoC 的强正规化：** 有 Altenkirch 早年在 LEGO 中的形式化，以及 Barras 在 Coq 中的工作。
- **groupoid 模型：** Lean 4 中有专门的项目在做。
- **sum-check 协议的可靠性：** 在 Lean 的密码学证明库中有形式化。

IP = PSPACE 全定理、Lamping 算法、Fagin、Haken、切换引理，我不知道有完整的形式化，但这是"我不知道"，不是"已核实没有"。
上面这些也只是我的记忆，没有逐一核对，外发前请自行确认。

## 二、这次已经完成的（M21 的第一块）

`Start/QbfArith.lean`，已接入 `Start.lean` 并在 `Start/Capstones.lean` 注册。无 `sorry`，公理只有
`propext`、`Classical.choice`、`Quot.sound`。

- `Complexity.Qbf.QBF.arith`：Shamir 的算术化，定义在任意交换环上。
- `Complexity.Qbf.QBF.arith_bool`：在 0/1 输入上恰好算出真值。
- `Complexity.Qbf.QBF.tqbf_iff_arith`：闭公式为真，当且仅当其算术化等于 1（在任何非平凡交换环中）。
- `Complexity.Qbf.QBF.arithPoly` / `.eval_arithPoly`：同一映射取值于 `MvPolynomial`，量词作用为代入。
- `Polynomial.card_eval_eq_le` / `.card_eval_eq_le_div`：sum-check 单轮可靠性。有限域上两个不同的、度数 ≤ d 的多项式
  至多在 d 个点上相等，所以在随机点上被骗的概率 ≤ d/|F|。

## 三、行的拆分（依赖关系）

### M21：IP = PSPACE

```
M21-QBF-ARITH ✔        M21-SUMCHECK-ROUND ✔
      │                     │         │
M21-QBF-SIMPLE-FORM         │   M21-FIELD-COBHAM
      │                     │         │
M21-LINEARIZE ──────► M21-SUMCHECK-GAME│
                            │         │
M21-IP-DEF ─────────► M21-VERIFIER-POLY
                            │
                      M21-TQBF-IN-IP ──► M21-PSPACE-SUBSET-IP ─┐
M14-SPACE-COMPILE ✔ ► M21-COBHAM-TO-SPACE ► M21-IP-SUBSET-PSPACE ┴► M21-IP-EQ-PSPACE
```

`M21-IP-DEF` 的设计要点：验证者是 Cobham 项，输入为 (x, 当前记录, 随机串)；证明者是任意函数；接受概率用对随机串**计数**得到的
有理数表示，不引入测度论。

### M22：复杂度的其他块

- `M22-NONDET-PROG`（瓶颈）→ `M22-IMMERMAN-SZELEPCSENYI`
- `M22-SPACE-HIERARCHY`
- `M22-CONP-PH` → `M22-COOK-RECKHOW`
- `M22-RESOLUTION` → `M22-HAKEN-PHP`
- `M22-AC0-DEF` → `M22-SWITCHING-LEMMA`（Razborov 的计数/编码证明，无需概率论）→ `M22-PARITY-NOT-AC0`
- `M22-FAGIN`（`TODO_NEEDS_DESIGN`）：库里的 NP 是 Cobham 验证者，不是图灵机，所以困难方向的 tableau 需要重新设计。

### M23：λ 演算与类型论

- `M23-PTS` → `M23-FOMEGA` → `M23-COC-SN`；`M23-PTS` → `M23-HURKENS`
- `M23-ID-TYPES` → `M23-GROUPOID-MODEL` → `M23-UIP-INDEPENDENT`
- `M23-LAMBDA-MU`
- `M23-LEVY-FAMILIES` → `M23-LAMPING-ABSTRACT`（两行都是 `TODO_NEEDS_DESIGN`）。建议第一步只做"无需 bookkeeping 的片段"
  （例如 EAL 可类型化的项）上的抽象算法；完整算法和 Lawall–Mairson、Asperti–Mairson 的复杂度结果明确排除在这一行之外。

### M24：可计算性与逻辑

- `M24-ABSTRACT-LOB` → `M24-GL`；再加上 `M24-ARITH-THEORY`，得到 `M24-GODEL2-ARITH`
- `M24-OMEGA-MODELS`（Turing 理想 / Scott 理想 / 跳跃理想，Kleene 树）
- `M24-VAN-LAMBALGEN`、`M24-KUCERA-GACS`、`M24-K-TRIVIAL`
- `M24-HYPERARITH`（`TODO_NEEDS_DESIGN`，需要序数）

未开行、只记录在此的：Toda、#P 与 Valiant 永久式、Nisan–Wigderson、显式替换与 Melliès 反例、CBPV、
无穷 λ 演算与余归纳 Böhm 树、Solovay 完备性。

## 四、优先级建议（与原"只挑三个"的差异）

1. **IP = PSPACE：同意排第一，但顺序改为先 `PSPACE ⊆ IP`。** 这一半不依赖任何跨模型编译器。`IP ⊆ PSPACE` 放在
   `M21-COBHAM-TO-SPACE` 之后；后者本身价值很高，会同时解开 M15 的两行。
2. **"单步层"瓶颈值得作为一条独立主线：** `M14-QBF-STEP-PROG`、`M22-NONDET-PROG`、`M21-COBHAM-TO-SPACE`。TQBF 完全性、
   Krivine 空间类、Immerman–Szelepcsényi、空间层级、`IP ⊆ PSPACE` 这五个结果都卡在同一类工作上：给离线机写带程序并证明正确。
3. **groupoid 模型：可以做，但要先补 `M23-ID-TYPES`。** 库里并没有现成的 Id 类型。
4. **最优归约：我不建议列进前三。** Lamping 算法完整的正确性证明篇幅很大，建议先做 `M23-LEVY-FAMILIES`，把问题陈述清楚。
5. **性价比最高的短任务：** `M24-ABSTRACT-LOB`（很短）、`M22-RESOLUTION` → `M22-HAKEN-PHP`（自包含，不依赖机器模型），
   以及 `M24-OMEGA-MODELS` 中的 Kleene 树。Immerman–Szelepcsényi 的篇幅并不小，因为它要先有 `M22-NONDET-PROG`。
