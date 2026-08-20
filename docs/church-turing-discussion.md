# 关于「能否从自明公理推出 CT 论题」的一点看法

（本文是对项目讨论的记录。项目里**已被机器验证**的内容见文末"本仓库实际证明了什么"一节；本文其余部分是分析和判断，不是定理。）

## 一、总体上我同意你的结论

你的三分法——「从明确公理推出 CT：做到了」「公理自明：做不到」「绝对意义的证明：不可能」——我认为是准确的。特别是那句
"公理就是直觉本身"，抓住了要害：公理化没有消灭负担，只是把负担从"论题"搬到了"公理的恰当性"上。

下面是我想补充、以及想稍作修正的几点。

## 二、我认为最重要的一个区分：论题 vs. 被误当成论题的定理

日常讨论里，"CT 论题被证明了吗"这个问题经常同时指两件完全不同的事：

1. **模型等价定理**：λ 可定义 = 部分递归 = 图灵可计算。这是纯数学命题，有证明，可以（而且已经）被机器逐步验证。
2. **论题本身**：非形式的"有效可计算" = 上述这个类。这里有一侧是非形式的，所以它连"待证命题"的资格都不具备——
   它不是假的，也不是未证的，它是**不可形式化的**。

这个区分之所以关键，是因为第 1 类结果的堆积（无论堆多少）在逻辑上对第 2 类**没有增量**，只在认识论上有增量。
把两者混为一谈，才会产生"证据这么多了，为什么还叫论题"的困惑。

## 三、对现代公理化工作的评价：它们是表示定理

Dershowitz–Gurevich、Gurevich 的顺序 ASM 论题、Sieg 的公理化、Moschovakis 的 recursor——我认为这些工作的
数学身份最好被描述为**表示定理**（representation theorem）：

> 若一个对象满足公理 A₁–A₃（顺序时间 / 状态是同构不变的一阶结构 / 有界探索），则它可被图灵机模拟。

这类定理的结构和数学里常见的表示定理完全一样（例如：满足某组公理的赋值一定来自某个绝对值；满足某组公理的
测度一定是 Haar 测度）。这类定理是真结果，值得认真对待。但它们回答的问题是"**满足这些公理的东西有多强**"，
而不是"**算法是否恰好就是满足这些公理的东西**"。后一个问题不是数学问题。

所以我不太赞成把它称作"循环"（circularity）。循环意味着论证有缺陷；这里的论证没有缺陷，缺的是**充分性判断**
（adequacy），而充分性判断在数学里从来就不是被证明的东西——它是被接受的。

## 四、我认为"自明性"这个要求本身被过度苛求了

一个常被忽略的对照：我们从不要求"连续性的 ε–δ 定义"是自明的，也不要求"可测""紧致""维数"的定义是自明的。
我们对定义的要求从来是**稳定、有产出、与前理论直觉的判例吻合**，而不是自明。CT 论题受到的特殊待遇，来自它
恰好在一个我们对前理论直觉抱有强烈信心的地方（"什么叫按步骤照做"），因而人们期待一个更强的答案。

如果把对 CT 的要求降到我们对待其他数学定义的同一水平，那么它早在 1936 年就已经"结案"了。它之所以仍被称为
论题，我认为主要是社会学的、以及 Gödel 遗留的期待所致，而不是因为它的证据比"ε–δ 抓住了连续性"更弱。

## 五、对"稳健性"论证的一个修正

你说稳健性是最强的证据，我同意。但稳健性论证有一个已知的弱点值得写明：**标准模型大多出自同一批人、同一批
直觉**，所以"图灵机、λ 演算、递归函数给出同一个类"这件事，部分地是共同直觉的产物，作为独立证据要打折扣。

真正有分量的是那些**动机上与"计算"无关**的刻画，最后仍落进同一个类：

- Diophantine 集合 = 递归可枚举集（MRDP / Hilbert 第十问题）；
- 群论中的字问题、半 Thue 系统、Post 对应问题；
- 元胞自动机、tag 系统等极简系统的普适性；
- 一阶逻辑可证性的枚举。

这些来自数论、群论、组合、逻辑的入口，事先没有理由与"人按步骤照做"重合。它们的重合，比十种图灵机变体的
重合有力得多。我会把"自然类"（natural kind）的论证主要押在这一层上。

## 六、两处我会措辞更保守的地方

1. **物理 CT 与数学 CT 要分家。** Malament–Hogarth 时空、相对论计算这类构造，即便成立，冲击的是"物理可实现的
   计算 = 图灵可计算"这条物理论题，而不是关于"有效程序"的数学论题。混在一起容易让人误以为数学论题有物理反例。
   另外量子图灵机与经典图灵机在**可计算性**层面同类，差别在复杂性——这一点你已经写对了，值得强调。
2. **公理的争议性不等于结论的脆弱性。** 即使有界探索之类的公理排除了某些指针式或共享内存式模型，那些模型
   实际上也没有算出图灵机以外的函数。也就是说：公理之争影响的是"这个定理覆盖了多少种算法概念"，而不是
   "算法可能超出图灵可计算"。这两件事在讨论中经常被合并，我认为应当分开。

## 七、我的结论

- **CT 论题本身：不需要、也无法在 Lean（或任何形式系统）中被证明。** 任何看上去像"证明了 CT"的形式化，都必然
  是把非形式的一侧替换成了某个形式定义，于是证明的是一条表示定理，而"替换是否忠实"重新成为一条论题。
  Gurevich 本人对 ASM 论题也是这么说的。
- **值得形式化的，是它周围的数学。** 这正是本仓库在做的事：模型等价（λ ⇔ 部分递归 ⇔ 图灵机）以及由此得到的
  不可判定性结果。这些是真定理，能被机器逐行检查，也是这场讨论中唯一能被"检查"的部分。
- 一句话概括我的立场：**CT 论题不是一个证据不足的定理，而是一条被误认为定理的定义性判断；它的地位不因证据
  增加而改变，只因我们对"定义能否被证明"这一问题的态度而改变。**

## 八、本仓库实际证明了什么（均无 `sorry`，仅依赖 `propext, Classical.choice, Quot.sound`）

- `lambdaComputable_iff_partrec`（`Start/PartialCapstone.lean`）：ℕ 上的**部分**函数是 λ 可定义的，当且仅当它是
  部分递归的。
- `TM2Partrec.tm2Computable_iff_partrec`（`Start/TM2Capstone.lean`）：ℕ 上的部分函数可被（打包的）图灵机计算，
  当且仅当它是部分递归的。
- `lambdaComputable_iff_tm2Computable`（`Start/TM2Capstone.lean`）：两个模型给出同一个类——即第五节意义上的
  稳健性的一个机检实例。
- **本次新增之一**（`Start/Undecidable.lean`）：`Lambda.not_computablePred_codeConverges`——
  没有可计算谓词能判定"一个（编码给出的）λ 项是否归约到某个 Church 数码"。也就是 **λ 演算版本的停机问题不可判定**。
  证明方式是归约：万有部分递归函数经由 `lambdaComputable_of_partrec` 得到 λ 实现子 `haltTerm`，而
  `k ↦ encode (haltTerm (church k))` 是原始递归的，于是可判定性将判定停机问题，与
  `ComputablePred.halting_problem` 矛盾。附带的非平凡性检查：`codeConverges_church`（Church 数码收敛）与
  `not_codeConverges_omega`（`omega` 不收敛）。
- **本次新增之二**（`Start/FixedPoint.lean`）：Turing 的不动点组合子 `Θ = A A`（`A = λx y. y (x x y)`）及
  `Lambda.Theta_reduces`——对任意项 `F`，`Θ F` **归约到**（不只是 β 等价于）`F (Θ F)`；推论
  `Lambda.exists_fixed_point`：任意项都有不动点。
- **本次新增之三**（`Start/SecondRecursion.lean`）：`Lambda.exists_code_fixed_point`——**Kleene 第二递归定理的
  λ 版本**：任意闭项 `F` 都存在项 `X`，使 `X` 归约到 `F ⌜X⌝`，其中 `⌜X⌝` 是 `X` 自身编码的 Church 数码。
  构造只用到一个实现子：对角函数 `c ↦ app_code c (church_code c)` 是原始递归的，因而由本仓库的
  `exists_realizer_of_computable` 得到闭的 λ 实现子。
- **本次新增之四**（`Start/NormalizationUndecidable.lean`）：`Lambda.not_computablePred_codeHasNormalForm`——
  **是否存在范式（normalizability）不可判定**，这是比"是否归约到 Church 数码"更强、也更标准的说法。关键在于
  本仓库的严格实现子在被模拟的计算发散时**连弱头范式都没有**（`partialTerm_not_hasWhnfEval`），因而更没有范式；
  `Lambda.exists_strict_realizer` 把这两半打包成一条可复用的引理。非平凡性检查：`codeHasNormalForm_church` 与
  `not_codeHasNormalForm_omega`。

## 九、如果要继续证，我会选什么

按"能被机器检查、且与上面讨论真正相关"的标准排序：

1. ~~λ 演算中的递归定理~~——**已完成**（见第八节：`Lambda.Theta_reduces`、`Lambda.exists_code_fixed_point`）。
2. ~~**Scott–Rice 定理**~~——**已完成**（`Start/Scott.lean`，见第十节）。此前以为它需要一个 λ 层面的自
   解释器 `E`（`E ⌜X⌝ ↠ X`）；事实上不需要：仅凭第二递归定理即可对角化。自解释器本身也~~仍然值得做~~
   **已完成**（`Start/SelfInterpreter.lean`，见第十一节），它是更精细的分离（Böhm-out）方向的入口。
3. ~~**Kleene 的 s-m-n 定理在本仓库编码下的一致（uniform）版本**~~——**已完成**（`Start/SMN.lean`，
   见第十节）。
4. ~~**一条表示定理的形式化**（Dershowitz–Gurevich 风格的"有界探索 ⇒ 可被图灵机模拟"的一个精简版本）~~——
   **已完成**（`Start/AlgorithmRepresentation.lean`，见第十二节）。这是唯一能把第三节的讨论从散文变成
   定理的做法；但正如第三节与第七节所述，做完之后得到的仍然只是表示定理，而不是 CT 论题的证明。

## 十、Scott–Rice 与 s-m-n（后续补上的两条）

- `Lambda.scott_theorem`（`Start/Scott.lean`）：**Scott 定理**。设项类 `A` 对可转换性封闭
  （`Lambda.ConvInvariant`，其中 `Lambda.Conv s t` 定义为"有公共归约式"，由 Church–Rosser 即 β 等价），
  且有一个闭项属于 `A`、另一个闭项不属于 `A`，则没有任何闭 λ 项 `F` 能判定 `A`——这里"判定"指
  `F ⌜X⌝ ↠ true`（当 `X ∈ A`）、`F ⌜X⌝ ↠ false`（当 `X ∉ A`）。证明是标准的对角化：取
  `G = λc. if F c then N else M`，由第二递归定理得 `X ↠ G ⌜X⌝`，于是 `X` 归约到 `N` 或 `M`，
  与封闭性矛盾。两个见证项必须是闭项，否则对角项本身不闭。
- `Lambda.not_computablePred_codeSet`（同文件）：**λ 演算版 Rice 定理**。同样条件下，`A` 中各项的
  编码集不是可计算谓词。这一步把"可计算"降到"λ 可判定"：由 `exists_realizer_of_computable` 把特征函数
  实现成闭项，再用 `isZero` 把 Church 数码变成布尔值，然后套用 Scott 定理。
- 非平凡性实例：`Lambda.not_computablePred_codeSet_conv_church_zero`——"是否与 `church 0` 可转换"
  不可判定；见证项是 `church 0`（属于）与 `omega`（不属于，因为 `omega` 与任何范式都不可转换）。
- `Lambda.exists_smn`（`Start/SMN.lean`）：**s-m-n 定理的一致版本**——存在原始递归的 `s`，使
  `s ⌜F⌝ n` 恰为 `F (church n)` 的编码。此前这一事实散落在若干归约论证里，现在是一条可复用的定理。

值得强调的是：即使把第 4 条做完，得到的仍然是表示定理，而不是 CT 论题的证明。这与本文第七节的结论一致。

## 十一、λ 层面的自解释器（后续补上的一条）

- `Lambda.exists_self_interpreter`（`Start/SelfInterpreter.lean`）：存在**一个闭项** `E`，使得对每个
  闭项 `M` 都有 `E ⌜M⌝ ↠ M`，其中 `⌜M⌝ = church (encode M)` 是 `M` 的 Gödel 码的 Church 数码。
  注意结论是**归约**，不只是 β 等价。
- 构造是标准的传环境解释器，用 Turing 不动点组合子 `Lambda.Theta` 打结：

      Ev = Θ (λ ev c e. if tag c = 0 then e (arg c)
                        else if tag c = 1 then (ev (left c) e) (ev (right c) e)
                        else λ x. ev (arg c) (extend e x))

  其中 `tag/arg/left/right` 是本仓库编码的数值析构函数；它们可计算，于是
  `exists_realizer_of_computable` 直接给出所需的闭 λ 实现子——没有引入任何新假设。
- 一般形式是 `Lambda.selfEval_correct`：对**任意**（可以是开的）项 `t` 与实现代换 `u` 的环境项，
  解释器归约到平行代换 `Lambda.substEnv u t`。抽象的那一支需要在 λ 之下归约，这正是必须引入环境
  参数、而不能只谈闭项的原因。
- 与 `Lambda.eval_gk` 的区别：后者是码到码的（算术化的求值器），前者是码到**项**的，即真正的
  自解释。
- 反方向不成立：`Lambda.not_exists_quote`——没有任何项 `Q` 能对所有闭项 `M` 给出 `Q M ↠ ⌜M⌝`。
  原因是归约无法区分一个项与它的归约结果，而编码可以（`I` 与 `I I`）。也就是说，解释（码 → 项）
  可以 λ 定义，引号（项 → 码）不行。
- 非空洞性检查：`Lambda.exists_self_interpreter_church`——在 `church k` 的码上，解释器还回 `church k`。

## 十二、表示定理与其余四条后续方向（里程碑 M5）

第九节第 4 条所说的表示定理，以及 README 中列出的其余"可能的下一步"，现在都已作为任务板里程碑 `M5`
完成。全部无 `sorry`，公理审计只用到 `propext, Classical.choice, Quot.sound`（`Lambda.not_solvable_omega`
只用到 `propext`）。

### 1. Dershowitz–Gurevich 风格的表示定理（`Start/AlgorithmRepresentation.lean`）

- `SeqAlgorithm.Algorithm`：一个"有界探索"形式的顺序算法——有限多个存放自然数的位置（`Fin size`），
  一张有限的**带守卫的同时赋值规则**表 `List (Rule size)`，以及指定的输入、输出、停机位置。
  状态即 `Fin size → ℕ`；一步转移 `stepProg` 取第一条守卫为真的规则并同时执行它的更新。
- 关键的一点是：**转移的可计算性是被证明的，而不是被假设的**——`SeqAlgorithm.primrec_stepProg`
  由规则表的有限性直接推出。这正是表示定理该有的形状：公理只谈"有界探索 + 顺序时间"，可计算性是结论。
- `SeqAlgorithm.Algorithm.partrec_run`：算法的输入–输出部分函数（迭代转移直到停机位置非零，再读出
  输出位置）是**部分递归的**；由本仓库的两条 capstone 立即得到
  `Algorithm.lambdaComputable_run`（λ 可定义）与 `Algorithm.tm2Computable_run`（图灵机可计算）。
- 非空洞性：`SeqAlgorithm.doubling` 是一个真会循环的算法，`SeqAlgorithm.run_doubling` 证明它算的是
  `n ↦ 2n`。
- **诚实的界限**：这是关于所述公理的表示定理，不是 CT 论题的证明。"这组公理是否恰好刻画了非形式的
  '算法'"不是数学问题；此处的位置模型（有限多个自然数寄存器）也比 Gurevich 的一阶结构状态更窄。

### 2. 带参数的递归定理（`Start/RecursionParams.lean`）

`Lambda.exists_recursion_with_parameters`：对闭项 `F`，存在**原始递归**的 `s`，使得对每个 `y`，
`decode (s y) = some X` 且 `X ↠ F ⌜s y⌝ ⌜y⌝`。即第二递归定理的不动点可以随参数原始递归地给出。

### 3. 多参数与其他输入编码（`Start/Encodings.lean`）

- `lambdaComputable2_iff_partrec₂`、`lambdaComputable2_iff_tm2Computable`：柯里化二元函数版本的模型等价。
- `LambdaComputableEnc` / `TM2ComputableEnc`：对任意 `Primcodable` 的输入与输出类型，经其编码定义可计算性，
  并证明 `lambdaComputableEnc_iff_partrec`、`tm2ComputableEnc_iff_partrec`、
  `lambdaComputableEnc_iff_tm2ComputableEnc`。这说明第五节意义上的稳健性不依赖于"只看 ℕ → ℕ"。
- 顺带把编译器加强为产出**闭项**（`Start/PartialCapstone.lean` 的 `lambdaComputable_of_partrec_closed`）。

### 4. 复杂度敏感的机器翻译（`Start/TM2PolyTime.lean`）

- `TM2Partrec.HaltsWithin`、`TM2ComputableNatInTime`、`TM2ComputableNatInPolyTime`：带时间界的机器实现；
  `lambdaComputable_of_tm2ComputableNatInPolyTime` 把多项式时间机器搬到 λ 侧。
- 与 mathlib 的对接：`partrec_of_tm2ComputableInPolyTime`、`haltsWithin_of_tm2ComputableInPolyTime`。
- **界限**：只做了"从多项式时间机器出来"的方向；保资源的**反向编译**（以及 λ 侧的代价模型）没有做，
  因此这里得到的是可计算性层面的结论，不是复杂性类的等价。

### 5. 可解性理论（`Start/Solvability.lean`）

- `Lambda.Solvable`：存在闭参数表使 `t` 应用之后与 `I` 可转换。`convInvariant_solvable` 说明它是
  可转换性不变的，于是第十节的 Scott–Rice 机器直接适用。
- `Lambda.not_solvable_omega`：`Ω` 不可解（只依赖 `propext`）。
- `Lambda.exists_args_conv_of_solvable`：**一般可达性**——可解项可以被闭参数驱动到任意闭项。
- `Lambda.not_decides_solvable`、`Lambda.not_computablePred_codeSet_solvable`：可解性不可判定。
- **界限**：Böhm 分离定理本身**没有**证明。这里给出的是可解性、它的不可判定性和一条一般可达性，
  而不是"两个不同的 βη 范式可以被同一个上下文分离"。

## 十三、Kolmogorov 复杂度（里程碑 M6）

算法信息论的三个前提——编码、通用机、停机不可判定——在本仓库都是已证的定理，因此 K 复杂度可以直接
在 λ 演算内部定义并展开。程序长度取项的语法规模 `Lambda.size`（节点数，De Bruijn 下标 `i` 计 `i+1`），

```
Lambda.kolm s = sInf { size t | t 闭 且 t ↠ church s }
```

`church s` 本身就是一个程序，所以下确界的集合非空、定义良基（`Lambda.exists_program_of_kolm` 给出最短程序）。

### 1. 不可压缩数存在（`Lambda.exists_incompressible`）

纯计数：规模 ≤ n 的项只有有限多个（`Lambda.finite_setOf_size_le`，按变量/抽象/应用逐层覆盖），
而由合流性（`Lambda.unique_church_reduct`）一个项至多归约到一个 Church 数码，于是复杂度 ≤ n 的自然数
也只有有限多个（`Lambda.finite_setOf_kolm_le`）。ℕ 无限，故任意 n 都有 `n ≤ kolm s`。

### 2. K 不可计算（`Lambda.not_computablePred_kolm_le`、`Lambda.not_computable_kolm`）

Berry 悖论，通过第二递归定理实现。为此把 `Start/SecondRecursion.lean` 的不动点加强为**闭项**版本
（`Lambda.exists_code_fixed_point_closed`），否则不动点不能充当"程序"。若关系 `kolm s ≤ n` 可判定，
则"求最小的、复杂度超过 `2c+1` 的 s"是部分递归而且处处有定义（用第 1 条），于是有闭 λ 实现子 `G`；
闭不动点 `X ↠ G ⌜X⌝` 便是某个数 m 的程序，而按构造 `kolm m > 2 · encode X + 1 ≥ size X`，矛盾。
这里唯一需要的"规模核算"是 `Lambda.size_le_encode : size t ≤ 2 · encode t + 1`，不需要把项规模在码上
做成可计算函数。

注意陈述的形式：对**固定**的 n，`{s | kolm s ≤ n}` 是有限集，因而可判定；不可判定的是二元关系。

### 3. 不变性定理

- λ 内部、真正加性的版本：`Lambda.kolm_le_kolmWith`——以任意闭项 `U` 当解释器（程序是满足
  `U p ↠ church s` 的闭项 `p`），复杂度至多下降常数 `size U + 1`；恒等解释器给回 `kolm` 本身
  （`Lambda.kolmWith_I_le_kolm`、`Lambda.kolm_le_kolmWith_I`）。
- 跨模型版本：任意部分递归的"描述系统" `V` 都满足 `kolm s ≤ 3p + c`（`V p = s` 时），
  常数由 `lambdaComputable_of_partrec_closed` 的闭实现子给出；再经
  `TM2Partrec.tm2Computable_iff_partrec` 得到图灵机版本 `Lambda.exists_const_kolm_le_of_tm2`。
  因子 3 是**一元** Church 数码的代价（`size (church p) = 3p + 3`）。
- 用二进制紧凑数码消掉这个因子：`Start/KolmogorovBinary.lean` 造出规模 `O(log n)` 的闭项
  `Lambda.binNum n ↠ church n`（用 `mult (church 2)` 与 `succ` 沿二进制展开构造），于是
  `Lambda.exists_const_kolm_le_size_of_partrec`：`kolm s ≤ c · (bit 长度 p + 1)`。

### 4. 界限（诚实说明）

- 就**节点数**这个尺度而言，不变性已经是加性的（`Lambda.kolm_le_kolmWith`）；就 **bit 长度**而言
  只得到"至多相差常数倍"，因为紧凑数码的每一个 bit 都要花掉常数个节点。要得到教科书里
  `K(s) ≤ |p| + c` 那种按比特计长的加性陈述，需要一个以比特计长的程序尺度；前缀复杂度还要求它
  是**自定界（前缀无关）**的，而现有编码是单射但不是前缀无关的。
- 同一个缺口挡住了 Chaitin Ω：没有前缀无关性，`Σ 2^{-|p|}` 没有理由收敛，Ω 甚至无法定义。
  任务板上 `M6-KOLMOGOROV-OMEGA` 记录了这条开放项及其设计要求（前缀无关编码 → Kraft 不等式 →
  前缀复杂度 → Ω）。Martin-Löf 随机性、Solovay 函数等更属于另一个量级的项目。
