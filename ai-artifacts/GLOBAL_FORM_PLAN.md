# global_form：计划（rev 4，2026-11-11，已实现；与代码同步）

**2026-11-23 加了第 8 节：一个开关，和在它之下运行的几个命令。**第 1 至 7 节是 2026-11-11 的状态，没有改；与第 8 节不一致的地方以第 8 节为准，
主要是：1.1"消费者只有一个""本 feature 只碰 Pure，对 HOL 零改动"、第 4 节的 base 与链、3.5 的 `global_form_result`、第 5 节的测试 1 与 14。
原来做这个 feature 的会话已不在；第 8 节由 concept A1 会话做（作者 2026-11-23 04:00 UTC：「交给你来做」）。

标记：【已定】= 作者已批；【提案】= 我提的、作者未表态；【未核实】= 只凭读源码推断，实现时要用测试验证。
行号按 `Isabelle2026/pristine`；本 feature 的 base（见 §4）没有改动这里引用的任何文件。

## 1. 这个 feature 是什么

`global_form` 是给 Isabelle Pure 加的一个 ML 级 local theory 操作。它包住一段 local theory 操作 `f`；在 `f`
运行期间，被包的 local theory 的各层 context 以及由它们派生的一切 context 里，假设不在 `Assumption` 数据中，
`f` 结束后放回原位。于是 `f` 里 note、define、declaration 的结果按 theory target 的方式存：不贴任何假设作前提，
固定变量照常泛化；forked 证明也不把假设打包进它的命题。

```ML
(*in signature LOCAL_THEORY*)
val global_form_result: (local_theory -> 'a * local_theory) -> local_theory -> 'a * local_theory
val global_form: (local_theory -> local_theory) -> local_theory -> local_theory
```

调用者的契约：`f` 的内容不依赖 context 的假设。违约时的行为见 §3.6。

【已定】真的从 `Assumption` 数据里取走再放回，不是设标志；【已定】上面两个签名；【已定】没有查询"是否处于
global_form 中"的函数；【已定】没有用户级命令（`tests/` 里只供测试、不发布的命令不算，作者 2026-11-11 批）；
【已定】单独一个 feature、单独一份计划。

### 1.1 起因与消费者

concept（一元 light locale，`contrib/light_locale`）块里的 `datatype` 导出的 `tr.exhaust`、`tr.induct` 等规则最前
多一条 `C ?S` 前提，`?S` 只在这一条里出现；在没有该 concept 的结构的上下文里这条前提既无法满足又关不掉。
datatype 的内容只依赖类型变量，从不依赖块的项参数，所以它的定理本该按 theory target 的方式存。

消费者只有一个：`contrib/local_datatype` 对 `bnf_fp_def_sugar.ML` 的补丁，在 `datatype`、`codatatype` 入口处、
**仅当当前 target 是 concept 时**包 `Local_Theory.global_form`（【已定】）。这处改动属于 local_datatype，
不属于本 feature；本 feature 只碰 Pure，对 HOL 零改动。

现状（2026-11-11）：Isabelle2026 上 `.gitmodules` 声明的链是 pristine → bicompose_rename_fix →
fast_abbrev_printing → sledgehammer_fact_trigger → light_locale → local_type_abbrev → localized_record →
local_datatype → dot_syntax，但 local_type_abbrev、localized_record、local_datatype 三棵 2026 树还停在
pristine，light_locale 的树只合并到 fast_abbrev_printing，concept 的 API 还是未提交的工作。所以"concept 块里
datatype 的规则不带 `C ?S`"这条验收目前跑不了；本 feature 先用 stock locale 下的 datatype 测试覆盖 BNF 一侧
（§5），concept 一侧留给 local_datatype 接入时验证。【已定】conda 发布暂缓。

### 1.2 不做的事

不提供用户级命令；不改任何 target 的 `notes`、`define`；不改 `Generic_Target`、`Goal`、`Thm`、
`Global_Theory`；不对"结果仍带 hyps"做任何检查（【已定】，理由见 §3.6）；不接受非 local theory 的 context；不支持 class target、`instantiation`、
overloading（【已定】，见 §3.7）；不做 Isabelle2025-2（【已定】）。

## 2. 一个运行例子

```isabelle
locale L = fixes S :: "'a set" assumes ne: "S ≠ {}"
context L begin
  (* A *) lemma a: "∃x. x ∈ S" using ne by auto              (* 普通：L.a: L ?S ⟹ ∃x. x ∈ ?S *)
  (* B *) ML 级：Local_Theory.global_form (note b = refl[of S])   (* L.b: ?S = ?S，没有 L ?S 前提 *)
  (* C *) ML 级：Local_Theory.global_form (note c = ne)          (* 调用者违约；kernel 报错 *)
  (* D *) lemma d: "∃x. x ∈ S" using ne by auto              (* 放回之后与 A 相同 *)
end
```

locale `L` 的 context 假设是 locale 谓词 `L S`（`locale.ML:545`），fact `ne` 是带 hyp `L S` 的定理。
B：`f` 运行时 `Assumption.all_assms_of lthy` 为空，stock 的 `Generic_Target.thm_definition`
（`generic_target.ML:307-357`）里 `Local_Defs.export` 贴不上任何前提，`Variable.export` 把 `S` 泛化成 `?S`，
导回本地时没有假设要 `COMP`，本地形式就是全局形式实例化到 `S`。
C：`ne` 的 hyp `L S` 没有人消去；`Variable.export`（`generic_target.ML:322-325`）要泛化 `S`，而 `S` 出现在 hyp
里，`Thm.generalize` 抛 `THM "generalize: variable free in assumptions"`（`thm.ML:1862-1863`）。

## 3. 设计

### 3.1 取走的是什么：假设取走，定义留下 【已定】

`Assumption` 数据里除了真正的假设，还有不是假设的条目，必须留下：

- `Local_Defs.define` 加的定义（`local_defs.ML:103-115`，export 是 `def_export`）。stock 的
  `Generic_Target.define`（`generic_target.ML:254-292`）每定义一个常量 `c`，就在最上层 lthy 里固定一个变量 `c`
  并加一条 `c ≡ C.c S`；此后块内提到 `c` 的定理导出时靠这条 export 把 `c` 展开成 `C.c S`。若把它也取走，`c`
  会被 `Variable.export` 泛化成无关的 schematic variable，得到错误的定理而不报错。这种条目只存在于最上层
  lthy，且只活到当前命令结束（每条 local theory 命令结束时 `Local_Theory.reset`，`local_theory.ML:167`，此后
  `c` 只是 target 上的 abbreviation）；所以只有同一个 ML 操作里先 `define` 再 `global_form` 才会遇到它。
- `defines` 元素加的定义（`Element.init (Defines …)`，`element.ML:464-473`）：locale 声明里的 `defines`
  （`locale.ML:547`）和 `context … defines … begin`。这是唯一跨命令存活的定义条目，也是消费者会遇到的。
- `Local_Defs.fixed_abbrev` 加的条目（`local_defs.ML:120-130`，cterm 列表为空，export 只做项展开）。

规则：**一个条目留下，当且仅当它的每个 cterm 都是定义；其余取走。**"cterm `A` 是定义"指：`A` 形如 `x ≡ t`
（`x` 是 `Free`），且该条目自己的项 export 会改写 `x`。cterm 列表为空的条目按此规则自然留下。

设计需要的不变式：取走之后，`Local_Defs.export lthy thy_ctxt` 返回的 `asms` 为空，且每条定义都还在。论证：留下的
条目的每个 cterm 都被自己的 export 改写其头变量，整段项 export 是各条目项 export 的复合，定义的头变量是该
context 新固定的、不会被别的条目再改回，所以 `Local_Defs.export` 的判据（`local_defs.ML:142-158`）把它们全判为
`defs`；被取走的条目不在表里。

与 stock `Local_Defs.export` 的判据有两处有意的差别：(1) stock 先滤掉 sort constraint 形式的假设，这里把它当
普通假设取走；(2) stock 用 inner 到 outer 的整段项 export 判断，这里用条目自己的 export 判断——一条
`assume_export` 的 `x ≡ t`，即使 `x` 恰被另一条目定义，也是假设，要取走。

### 3.2 取走后放在哪：`assumption.ML` 里的第二个 `Proof_Data` 槽 【已定】

`Assumption` 原有的数据（`datatype data`、`map_data`、`add_assms`、全部读取与 export 函数）一行不动。新增一个
私有的槽，每个 context 自带：

```ML
structure Suspended = Proof_Data
(
  type T = (serial * data * data) list;   (*token, data before, data put in its place*)
  fun init _ = [];
);
```

- 取走（私有 `suspend token keep ctxt`）：同步走一遍 `rev_assms` 与 `rev_prems`（`add_assms` 是唯一写入者，
  `assumption.ML:133-140`，每个 cterm 恰好对应一个 prem，所以用库函数 `unflat` 把 prems 按条目分组），
  只保留 `keep` 为真的条目及其 prems，得到 `filtered`；把 `(token, old, filtered)` 压进槽，把 `filtered` 写回数据。
- 放回（私有 `resume token ctxt`）：槽顶的 token 与之相同时，设当前数据比 `filtered` 多出 `n` 个条目、`m` 个
  prems（`Assumption` 数据只增不减，所以多出的都在表头，是 `f` 期间新加的），写回
  `take n cur_assms @ old_assms`、`take m cur_prems @ old_prems`，弹出槽顶；槽里没有这个 token 时什么都不做。

为什么不存在 `global_form_result` 的局部值里：`f` 结束时的层与开始时未必是同一批 context。stock 的
`end_nested`（`local_theory.ML:452-456`）经 `reset` 把最上层 lthy 换成下一层的 target context；`f` 里一次平衡的
`begin_nested … end_nested` 之后，最上层 lthy 的表已不是开始时那张，按层号放回会塞错；而靠比较表来推断"这个
context 是哪一层变来的"有歧义（一层嵌套 `context assumes A` 与最上层 lthy 取走后的表可以一模一样）。槽跟着
context 走，开层、关层、`reset` 都不用特别处理。从不调用 `global_form` 时槽为空，所有 stock 路径逐字节不变。

嵌套的 `global_form`：每次调用用 `serial ()` 取一个新 token，放回只认自己的 token，所以内层只放回自己取走的。

`f` 里派生出来的 context（forked 证明的 context、被闭包或 `Lazy` 捕获的 context）继承取走后的数据，晚于 `f`
结束才运行的证明仍然看不到假设；它们不会被放回，这正是需要的行为。

范围的精确说法：只有被包的 lthy 的各层 context 及其派生 context 没有假设。`f` 里从头新建的 context（例如
`Locale.init`）仍带着假设；拿它与 `f` 的 context 做 export，两边的表对不上，stock 的 `check_result`
（`assumption.ML:108-113`）抛 `Fail "Outer context disagrees on assumption"`。`f` 内外的 context 之间做 export
同理。这是两个确实不一致的 context 应得的结果，不做兼容。

### 3.3 `assumption.ML` 的改动

纯新增：§3.2 的槽、两个私有函数，以及 signature 里**唯一**的新导出（名字【已定】）：

```ML
val suspend_result: (export * cterm list -> bool) ->
  ((Proof.context -> Proof.context) -> 'b -> 'b) -> ('b -> 'a * 'b) -> 'b -> 'a * 'b
```

`suspend_result keep map_ctxts f x`：取一个新 token；`x |> map_ctxts (suspend token keep) |> f ||>
map_ctxts (resume token)`。第二个参数是"把一个 context 变换作用到 `'b` 里每个 context 上"的函数，因为
`assumption.ML` 加载早于 `local_theory.ML`，不知道 local theory 的层结构。取走与放回不单独导出，写不出不配对的
用法。`keep` 为真表示该条目留下（与 `filter` 同向）。

### 3.4 `local_defs.ML` 的改动

从 `Local_Defs.export`（`local_defs.ML:142-158`）里抽出它判断"是定义"的核心作私有函数，两处共用：

```ML
(*the definition A, if term_export rewrites its head*)
fun defines_free term_export A = …   (*head_of_def, try, aconv: the code now inline in export*)
```

`Local_Defs.export` 保留自己的 sort constraint 过滤，改为调用它（传 `Assumption.export_term inner outer`），行为
不变。signature 新增（名字【已定】）：

```ML
val is_def_assms: Assumption.export * cterm list -> bool
```

`is_def_assms (e, As)` = `As` 的每个 cterm 都被 `defines_free (#2 (e false As))` 判为定义。

### 3.5 `local_theory.ML` 的改动

```ML
fun global_form_result f =
  assert #>
  Assumption.suspend_result Local_Defs.is_def_assms (map_contexts o K) f;

fun global_form f = #2 o global_form_result (f #> pair ());
```

`map_contexts`（`local_theory.ML:169-179`）作用于每一层的 target context 和最上层 lthy 本身。`assert` 必须有：
`map_contexts` 自己不检查，层数为 0 时会把变换作用到裸的 proof context 上。`f` 抛异常时旧的 lthy 值原封不动。

### 3.6 调用者违约时会发生什么 【已定：不加检查】

取走之后，导出不贴前提、forked 证明不打包假设，这是构造保证的。结果上还会有 hyp，只可能是 `f` 里的代码主动
用了假设对应的 fact（它仍在 fact 表里，是带 hyp 的定理），即调用者违约。kernel 的 hyps 记录保证不会因此得到
错误的无 hyp 定理。实际表现：

1. 同步 note，hyp 里有会被泛化的固定变量或类型变量（通常如此）：`Variable.export` 抛
   `THM "generalize: variable free in assumptions"`，不带 fact 名。
2. 同步 note，hyp 里没有这样的变量（例：`context assumes Q: "∀x::nat. x = x" begin`），有名无名都一样：
   全局 note 总带 `Thm.kind` 这个 attribute（`global_theory.ML:383`），`apply_attribute`
   （`more_thm.ML:689-690`）在 theory context 里查 hyps，报 `Undeclared hyps:`。
3. declaration 携带的定理（`Local_Theory.declaration`，含 pervasive 的 background declaration，
   `generic_target.ML:207-212`）：内容只经 export morphism 变换就存进 theory 或 locale 的数据。hyp 含固定变量
   时 morphism 抛 generalize 那条错；hyp 不含固定变量时**原样存下，没有任何检查。已知限制，不处理。**
   这是违约唯一不被察觉的渠道。
4. forked 证明用了假设的 fact：`Goal.future_result`（`goal.ML:112-146`）在 join 时失败——目标提到 hyp 里的
   固定变量时是 `forall_intr: variable "S" free in assumptions`（`goal.ML:135`，`thm.ML:1406-1408`）；只共享类型
   变量时是 generalize 那条；没有公共变量时是 `Thm.future_result` 的 `bad hyps`（`thm.ML:854-867`）。
   join 可能晚于 `f` 结束。
5. 带 hyp 的定理没有被 note，只是作为 `f` 的返回值流到 `global_form` 之外：放回之后它是一条普通的、依赖假设
   的本地定理，完全合法。

不加检查的理由（作者）：导出后带 hyps 本身可以是合法情况，一处常开的检查会误伤；本设计已通过构造保证了想要
的性质。`more_thm.ML` 的"已声明 hyps"表也不动。

### 3.7 对各 target 的效果

- theory target：没有可取走的条目，`global_form f` 与 `f` 行为相同。
- stock locale target：`notes` 的全局定理不带 locale 前提；`locale_notes` 仍把 fact 登记进 locale，重开 locale
  或 interpretation 时照常出现。`define`、`abbrev`、`declaration` 的参数来自固定变量，不受影响。
- concept target（light_locale）：`concept_notes` 的非"导出形式"分支调 `thm_definition`，得到不带 `C ?S` 的全局
  定理；它的"导出形式"分支只收无 hyp 的定理，不受影响；`concept_degeneracy_check` 的钩子只发 warning。
  这三点待 local_datatype 接入时在真实树上验证（§1.1）。
- 嵌套 `context fixes … assumes … begin`：该层的 `assumes` 一并取走。
- class target、`instantiation`、overloading：**不支持**（【已定】，作者 2026-11-11）。代码走同一套通用机制、
  没有专门禁止，但没有测过，行为不作保证。

`f` 运行期间，对被包的 lthy 及其派生 context 调 `Assumption.all_assms_of` 的工具（Sledgehammer、Nitpick、
`Skip_Proof`）看不到假设；Quickcheck 的 locale 模式拿 `Locale.init` 新建的 context 作 outer
（`quickcheck.ML:355`），会遇到 §3.2 说的 `Fail`。

## 4. 仓库与基线

- 仓库：`contrib/global_form`，GitHub `xqyww123/Global_Form`（public，已建）。
- 【已定】base = `Isabelle2026/sledgehammer_fact_trigger`（light_locale 声明的 base；分支与两棵树已建，
  stock 树在 release tag `Isabelle2026/sledgehammer_fact_trigger/1`）。之后 light_locale 的 base 改为
  `Isabelle2026/global_form`（SKILL 3.7，属于 light_locale 的会话），消费者 local_datatype 经链拿到本 feature。
  本 feature 的包因此依赖 sledgehammer_fact_trigger 的包。
- 分支 push：【已定】代码评审通过后。
- 补丁文件三个：`src/Pure/assumption.ML`（纯新增）、`src/Pure/Isar/local_defs.ML`、
  `src/Pure/Isar/local_theory.ML`。light_locale 当前的树里前两个文件与 pristine 相同，第三个它加了
  `redeclare_result` 等；合并冲突由 light_locale 一侧在换 base 时处理。
- `tools/signature_additions.txt`：`Assumption.suspend_result`、`Local_Defs.is_def_assms`、
  `Local_Theory.global_form_result`、`Local_Theory.global_form`。
- 只在 Isabelle2026 上做（【已定】）。

## 5. 测试（`tests/`，session `Global_Form_Test`，父 session HOL）

每条测试是 theory 里的 ML 断言，失败即 build 失败。Pure 级的测试用 locale `L`（§2）。

1. theory target：`global_form (note …)` 的全局定理与不包时的 `Thm.prop_of` 相同。
2. stock locale，note 不用假设的定理：全局定理没有 `L ?S` 前提，本地 fact 可用；`end` 后重开 locale 该 fact
   仍在；做一次 interpretation，fact 出现。
3. 违约，同步：note `ne`，断言错误文案含 `variable free in assumptions`。
4. 放回：`global_form` 之后 `Assumption.all_assms_of`、`all_prems_of` 在每一层都与之前逐项相同；之后的普通
   lemma 的全局形式带 `L ?S` 前提。
5. 定义留下，两种情况：(i) 带 `defines "D ≡ …S…"` 的 locale，在 `global_form` 里 note 一条提到 `D`、无 hyp
   的定理：全局定理里是右端在 `?S` 上的展开，没有 `Free D`、没有 `?D`、没有 locale 谓词前提。
   (ii) 同一个 ML 操作里 `Local_Theory.define … #> Local_Theory.global_form (note … c …)`：全局定理里出现的是
   `L.c ?S`。
6. `f` 里 `Local_Theory.define` 再 note 新常量的定理：成功，全局定理提到新的全局常量。`f` 期间新加的条目在
   放回后仍在最上面：用 `global_form_result` 把新常量带出来，同一个操作里断言假设与定义都在、prems 与 assms
   逐项对应，再 note 一条提到新常量的定理，其全局形式带 `L ?S` 前提、提到 `L.g ?S`、没有 `Free`。
   （测试 5 (i)、8 另在 `f` 内部断言留下的 prems 与留下的 assms 逐项对应。）
7. `f` 里平衡的 `begin_nested … end_nested`，且同一个操作里先 `Local_Theory.define`，使最上层 lthy 有一条
   定义条目（§3.2 的例子）：同一个 `f` 包在 `global_form` 里跑一遍、不包跑一遍，两次结束后各层 target context
   与最上层 lthy 的 `Assumption.all_assms_of`、`all_prems_of` 逐项 aconv。
8. 嵌套 context（`context L begin context fixes y assumes "P y" defines "d ≡ …y…" begin`）：两层的假设都被取走、
   都放回；`global_form` 里 note 的提到 `d` 的定理里 `d` 被展开，且没有 `P ?y` 前提。
9. 嵌套 `global_form (… global_form g …)`：内层结束后外层仍处于取走状态（外层 `f` 的后半段
   `Assumption.all_assms_of` 仍为空），外层结束后全部放回。
10. forked 不违约：对 `global_form` 里的 context 调 `Goal.future_result ctxt (Future.value th) prop`，`th` 无
    hyp：结果无 hyp、无前提。（直接调 `Goal.future_result`：`Goal.prove_future` 是否真的 fork 取决于当时负载，
    不 fork 时测试空过。）
11. forked 违约：同上，`th` 带 hyp `L S`、`prop` 提到 `S`：断言错误文案含 `forall_intr`。
12. `f` 返回带 hyp 的定理而不 note：`global_form` 之后 note 它，得到带 `L ?S` 前提的全局形式。
13. 非 local theory 的 context：`global_form` 报 `Missing local theory context`。
14. datatype 与 codatatype（BNF 一侧的验收）。`tests/` 里定义两个只供测试的命令，把
    `BNF_FP_Def_Sugar.parse_co_datatype_cmd`（`Least_FP`/`construct_lfp` 与 `Greatest_FP`/`construct_gfp`）的结果
    包进 `Local_Theory.global_form`。在一个假设提到参数与类型变量的 stock locale 里：定义一个 datatype、
    一个经 `list` 嵌套的 datatype、一个 codatatype；断言全局的 `induct`、`exhaust`、`coinduct`、`size`、`rel_*`
    等 fact 没有 `L ?S` 前提；`global_form` 返回之后强制所有 lazy fact；重开 locale 并做一次 interpretation。
    同样的类型不包时带 `L ?S` 前提，作正对照。
15. 违约，hyp 不含固定变量：theory target 上 `context assumes Q: "∀x::nat. x = x" begin`，在 `global_form` 里
    有名地、无名地各 note 一条由 `Q` 得到的定理：都报错，文案含 `Undeclared hyps`。

## 6. 实施步骤

状态截至 2026-11-11 18:30 UTC。

1. （已完成）建 GitHub 仓库、`git init`、`new-tree`。
2. （已完成）在私有树里改三个文件；写 `tests/`。
3. （已完成）build：Pure、HOL、`Global_Form_Test` 全过，15 条测试通过。
4. （已完成）代码评审通过，五条意见已改入；四个变异（全部留下、全部取走、放回时盖回旧表、取走时丢掉留下
   条目的 prems）都使 `Global_Form_Test` 失败；私有树提交 `c2858be`，分支已 push。
5. （已完成）`init.sh`、`tools/*.txt`、`tools/release_build.sh`、`.gitattributes`、README（作者已批）、LICENSE
   （BSD-3-Clause，作者已批）；发布检查清单五条与 `check-signatures` 通过。
6. 登记提交、push、MLML `git submodule add`：都按命令。
7. `make-patches` 发布按命令；conda 发布暂缓。之后通知 light_locale 的会话换 base、local_datatype 的会话接入。

## 7. 已知代价与风险

- 在 feature 树上 build HOL（测试 session 的父 session）：以小时计，需作者下令。`assumption.ML` 的改动是纯新增，
  不调用 `global_form` 的路径不变，这次 build 同时充当回归。
- §3.6 第 3 条的已知限制：declaration 携带的、hyp 不含固定变量的违约定理不被拦截。
- 违约的报错是 kernel 的原始文案，不带 fact 名；forked 的推迟到 join。
- concept 一侧的验收（§1.1、§3.7）要等上层 feature 的 2026 树就位。
- light_locale 换 base 时要合并 `local_theory.ML`。

## 8. 开关，和在它之下运行的命令（2026-11-23）

状态：代码在私有树里改好、测试通过，**未提交**；清单作者 05:25 UTC 定为六个（8.4B），代码与测试已照此；2026-11-23 05:4x UTC 送代码评审。文中时刻是 UTC。
8.2 与 8.3 写的是最终的样子；8.4、8.4A 是到达它的经过（其中"七个""`copy_bnf` 建议不包"等是当时的说法）。

### 8.1 作者定了什么

出处是 concept 的 A 区计划 `ai-artifacts/CONCEPT_A_DECLARATION_PLAN.md` 2.5（MLML 仓库）；那时本 feature 的会话已经关闭，所以一直没有做。
- 【已定，作者 2026-11-14】`global_form` 受一个开关控制：`Config.declare_bool` 建的布尔选项，没有 attribute，用户写不出；
  把 fact 存成全局形式的 target（concept 的块、实例上下文）在自己的 `setup` 里把它设为真。`global_form`、`global_form_result` 开着才取走假设，关着就是 `f`；不另加无条件的版本。
- 【已定，作者 2026-11-14】用到它的命令（"入口"）都并进本 feature，各自在入口处无条件地包一层 `global_form`；命令因此不认识 concept。
  入选的判据："证明全由包或内核生成、用户插不进 fact"。清单是九个：
  `definition`、`record`、`datatype`、`codatatype`、`primrec`、`primcorec`、`datatype_compat`、`copy_bnf`、`bnf`。
- 【已定，作者 2026-11-16「赞同 两处绕开 Pure.thy 的做法」】任何 `.thy` 文件都不改；`definition` 命令定义在 `Pure.thy`，所以包在它调的 `Specification.definition_cmd` 里。
- stock 的 locale 一字不改（作者 2026-11-11）：开关默认关着，所以 stock 的每一种 target 里这些命令与原来相同。

### 8.2 做了什么

- `src/Pure/Isar/local_theory.ML`：signature 加一行 `val global_form_enabled: bool Config.T`；
  `global_form_result f lthy` 先 `assert`，开关开着照 3.5 取走假设，关着就是 `f lthy`。
- 六个入口，各一处：
  - `src/Pure/Isar/specification.ML`：`definition_cmd` 包在 `Local_Theory.global_form_result` 里。ML 函数 `Specification.definition` 不包。
    在 Isabelle 自己的源码里 `definition_cmd` 只有 `definition` 命令这一个调用者（`Pure.thy`）；不改 `.thy` 文件就没有别的地方可以放这一行。
    配套的 AFP（`afp-2026-10-26`）里另有五个条目从 ML 调它（ConcurrentIMP、Optics、Isabelle_C、Isabelle_Meta_Model、Isabelle_DOF）：
    开关开着时它们存下的定义定理也不带前提，与 `definition` 命令相同。（2026-11-23 代码评审 `review_switch_1` 指出原来那句"只有一个调用者"只在 Isabelle 里成立，照改。）
  - `src/HOL/Tools/BNF/bnf_lfp.ML`（`datatype`）、`bnf_gfp.ML`（`codatatype`）、`bnf_lfp_rec_sugar.ML`（`primrec`）、
    `bnf_lfp_compat.ML`（`datatype_compat`）、`bnf_lift.ML`（`copy_bnf`）：在定义命令的那一行包 `Local_Theory.global_form`。各包的 ML 函数不包。
  - `primcorec` 一度包过（`bnf_gfp_rec_sugar.ML`），作者 05:25 UTC 定了不留，已撤回。
- 于是本 feature 不再"只碰 Pure"：补丁文件从三个变成九个，其中五个在 HOL。

### 8.3 测试与实测（`tests/Global_Form_Test.thy`；日志在 `ai-artifacts/nine_entries/`，不提交）

- 只供测试的命令 `global_form_enable`：在打开的 local theory 的每一层把开关设为真。它取代原来两个只供测试的命令（`global_form_datatype`、`global_form_codatatype`）。
  原有的测试里，在 local theory 的块里的（2 至 12、15）都先写它，断言不变；测试 1 在 theory target 上，开关写在它的 `local_setup` 里；
  测试 13 测的不是 local theory，不写（`global_form_result` 仍先 `assert`，所以它照旧）；测试 14 改写，见下。
- 新的测试：
  - 16：开关没开时 `global_form` 什么都不做（里面的假设还在，存下的定理带着 locale 的前提）。
  - 14（改写）、17、18、20、21：开着开关的 stock locale 块里，stock 的 `datatype`、`codatatype`、`definition`（用到 locale 的参数的、带 attribute 的、带条件的）、`primrec`、
    `datatype_compat`、`copy_bnf` 存下的定理都没有 locale 的前提。
  - 19：`primcorec` 不在 `global_form` 之下：开着开关的块里，它对一个在 `global_form` 之下定义的 codatatype 存下的定理带着 locale 的前提。
  - 22：这些命令之后假设都放回了（之后的 lemma 带着 locale 的前提）。
  - 每个包着的命令都有一个会带上前提的对照：同样的命令写在没开开关的块里（`datatype`、`codatatype`、`definition`、`primrec`、`copy_bnf`）；
    `datatype_compat` 的对照是在开着开关的块里直接调它没有包的 ML 函数。
    `definition` 另有一个同样的对照（评审之后加的）：在开着开关的块里直接调没有包的 ML 函数 `Specification.definition`，它存下的定理带着 locale 的前提；
    这一条钉住"包只在命令的入口，不在 ML 函数里"。
- **代码评审 `wf_507090bf-f6d`（2026-11-23 05:44 至 06:04 UTC；结果 `ai-artifacts/nine_entries/review_switch_1_result.json`，不提交）：通过**，五条验收标准都满足。
  留下的都判给维护者、不用再审，已改（06:1x 至 06:3x UTC）：
  - 8.2 里"`definition_cmd` 只有一个调用者"那一句只在 Isabelle 里成立，已照改（见 8.2）。
  - 本节两处措辞：哪些原有测试写了开关；Pure 是在哪一次构建里重建的。
  - 测试代码三处整洁：测试 17 里对变量先后的断言去掉多余的 `orelse`；测试 16 去掉多套的一层 `fn`；helper `facts_of_type` 改名 `facts_named`。
  - 裁判说可做可不做的两处，都做了：上面 `definition` 的那个对照；测试 20 里一行分辨不出 `datatype_compat` 包没包的断言（`.ls.eq.`）删去。
  - 驳回的一条：把五处 HOL 入口写成同一种拼法（裁判数了 Isabelle 自己 44 处命令入口的写法，现在的三种拼法各是那种形状的惯用写法）。
  改完之后 `Global_Form_Test` 在默认设置（`build_test_10.log`）与 `-o parallel_proofs=0`（`build_test_11_pp0.log`）下通过。
- 评审之前的最终的样子 2026-11-23 05:35 至 05:43 UTC 跑的：HOL 在改过的树上重建通过（`build_hol_3.log`；开关关着时这些命令走的是原来的路，这次构建同时充当回归）；
  Pure 的源码 04:05 UTC 之后没有再改，它是在 `build_hol_1.log` 里重建的，到 `build_hol_3.log` 时已是最新；
  `Global_Form_Test` 在默认设置（`build_test_7.log`）与 `-o parallel_proofs=0`（`build_test_8_pp0.log`）下通过。
  （七个入口时的那一版 04:1x UTC 也跑过：`build_hol_1.log`、`build_test_5.log`、`build_test_6_pp0.log`。）
- 没有做的：逐个去掉某一处的包、重建 HOL、确认测试失败（每个要重建一次 HOL，约 9 分钟）。上面的对照说明的是"包没有起作用时断言会失败"。
- 探针量到的（`ai-artifacts/nine_entries/Entries_Probe.thy`，结果 `entries_probe.out`、`build_probe_2.log` 至 `build_probe_4.log`）：
  - `copy_bnf` 对 theory 里定义的类型：没开开关时存 59 条定理、每条都带 locale 的前提；开着时 59 条都不带。
  - **`copy_bnf` 对同一个块里 `typedef` 出来的类型，开着开关时失败**：`typedef` 没有包，它的 `type_definition_…` 在块里带着 locale 的假设作 hyp（实测 1 条）；
    `copy_bnf` 的命令本身不报错，之后并行的证明在汇合时报 `future_result: bad hyps`（六条，不带位置），整个 theory 失败。这是 3.6 第 4 条说的违约情形。
  - `datatype_compat`：对不嵌套的 datatype，包不包存下的定理相同（四条，都没有前提，是在 theory 层登记的）；对嵌套的 datatype 它另外 note 几条规则，不包时带前提（测试 20 用的是这种）。
  - stock 就有的一处：没开开关的 locale 块里定义的 datatype，`datatype_compat` 失败（`TERM dest_equals`，case 的等式带着 locale 的前提）。开着开关时通过。

### 8.4 与清单不同的三处【等作者定】

1. **`record` 在这棵树里包不了。**这里的 `record` 还是 theory 层的命令（`Toplevel.theory`），不能写在任何 local theory 的块里，没有可包的地方。
   把它变成 local theory 命令的是 `localized_record`，在新的链里排在 concept 之后；那一行要加在那个 feature 里。
2. **`bnf` 不满足判据，没有包。**它是交出证明目标的命令（`local_theory_to_proof`），BNF 的各条公理由用户证，与定了不包的 `typedef` 同类。
   - 只包它证完之后的那一段不行：用户证出的定理在证明并行时带着全部假设，那一段一存就报错；不并行时只在证明用到假设时才报错。结果随证明是否并行而变。
   - 让整段（连同用户的证明）都不带假设，要把"取走"与"放回"拆成两个单独导出的函数，违背 3.3 定的"不单独导出，写不出不配对的用法"。
   - 建议：`bnf` 不包。
3. **`copy_bnf` 照清单包了，但它对块里 `typedef` 出来的类型会失败**（8.3 的实测），而"先 `typedef`、紧接着 `copy_bnf`"是它最常见的用法。
   它拿用户的 `typedef` 的定理作输入，严格说也不满足判据。
   - 不包的话：两种类型都能用，存下的定理带着 locale（concept）的前提。
   - 建议：`copy_bnf` 不包。

照建议做的话，本 feature 里包的是六个：`definition`、`datatype`、`codatatype`、`primrec`、`primcorec`、`datatype_compat`。

读代码推断、没有量的一处后果：块里的 `datatype` 若经一个"BNF 的定理依赖块的假设"的类型嵌套（如块里 `typedef` 之后不包的 `copy_bnf`、`bnf`、`lift_bnf` 登记的类型），会同样报 `bad hyps`。

### 8.4A 讨论与补量（2026-11-23 04:3x 至 04:5x）

作者 04:2x：对 8.4 的第 2、3 条「run Opus agent team 讨论一下」。Workflow `wf_66fe07f9-e7d`：三个提示词相同的 agent 各自作答，一个只比较异同并核有分歧的事实。
结果 `ai-artifacts/nine_entries/discussion_bnf_copy_bnf_result.json`（不提交）。

- **`bnf`：三方一致，不包。**理由与 8.4 第 2 条相同；另指出它在用户证明之前就定义了几个常量，只包后半段的话存下的东西一半带前提一半不带。`lift_bnf` 同理不包。
- **`copy_bnf`：一比二。**一方主张不包（同 8.4 第 3 条）；两方主张照清单包着，把"块里 `typedef` 之后 `copy_bnf`"写成不支持的用法。
  比较的一方核出两条 8.4 第 3 条没有算进去的代价（读源码），下面的探针量实了：不包的登记在块里、在 theory 里都不能再被 datatype 嵌套。
- 三方都认为入选的判据要写得更准，各拟了一句；其中两句会把已入选的 `primcorec` 也划成有疑问的（它对不平凡的互斥义务用上下文的 `auto`，与 `fun` 被排除的理由同类）。

**补量**（`ai-artifacts/nine_entries/nesting/`，四个探针 theory；`build_default.log` 与 `build_pp0.log`，04:55 UTC）。块是开着开关的 stock locale；"包着"指命令在开关开着时运行，"不包"用开关还没开时运行来代替。

| 情形 | 证明并行（默认） | `parallel_proofs=0` |
|---|---|---|
| A：包着的 `copy_bnf` 登记 theory 里的类型，块里的 `datatype` 经它嵌套，块外的 `datatype` 再经它嵌套 | 都通过；三组定理（118、70、125 条）没有一条带 locale 的前提 | 相同 |
| B：块里 `typedef`，再包着的 `copy_bnf` | 命令返回，之后六条 `future_result: bad hyps`，不带位置 | 在 `copy_bnf` 那一行报 `generalize: variable free in assumptions` |
| C：不包的 `copy_bnf` 登记 theory 里的类型，块里（包着的）`datatype` 经它嵌套 | 在 `datatype` 那一行报 `generalize: variable free in assumptions` | 相同 |
| D：不包的 `copy_bnf` 在块里登记 theory 里的类型，之后 theory 层的 `datatype` 经它嵌套（整个情形里开关没有开过，是 stock 的行为） | 在 `datatype` 那一行报 `CTERM Trueprop_conv`，命题是带着 `LP ?S ⟹` 的那条 | 在 `datatype` 那一行报 `Tactic failed` |

量出来的结论：
- 不包的登记（C、D）让那个类型的 BNF 带上块的前提，块里、块外的 datatype 都不能再经它嵌套；D 说明这在 stock 的 locale 里本来就是这样。`bnf`、`lift_bnf` 不包，同样如此（没有单独量 `bnf`）。
- 包着的 `copy_bnf` 对块外定义的类型是完整可用的（A）；对块里 `typedef` 的类型在两种运行方式下都失败（B），只是报错的地方不同。
- 所以 8.4 第 3 条"建议 `copy_bnf` 不包"**撤回**：不包并不是"两种都能用"，而是登记出来的 BNF 不能再用于嵌套。concept A1 现在的建议是照清单包着。

另一件相关的事实（concept 的树里量的，`concept_A_prototype/command_dev/build19.log`）：块里的 `typedef` 既不能提到块固定的变量，类型参数也不能是块里固定的类型变量，
所以它定义的类型与块无关；把 `typedef` 连同它的 `copy_bnf` 写在块外不损失什么（除非非空证明要用块的假设）。

**现在等作者定的**：`bnf` 从清单里拿掉；`copy_bnf` 留在清单里、"块里 `typedef` 之后 `copy_bnf`"记作不支持的用法；判据的措辞；`primcorec` 留不留。

### 8.4B 作者 2026-11-23 05:25 的决定，与随之做的

作者的原话：「赞同 bnf 从清单里拿掉；copy_bnf 留在清单里；」「既然如此，建议禁止在 concept (instance) context 中写 typedef，因为这是无意义的」「primcorec 不留」；对判据的措辞：「你可以自决」。

- **在 `global_form` 之下运行的命令定为六个**：`definition`、`datatype`、`codatatype`、`primrec`、`datatype_compat`、`copy_bnf`。
  `bnf` 没有包过；`primcorec` 的那一行已撤回（`bnf_gfp_rec_sugar.ML` 回到原样），测试 19 改成"它不在 `global_form` 之下，存下的定理带着 locale 的前提"。
  `record` 的那一行留给 `localized_record`（8.4 第 1 条）。
- **判据**【concept A1 定】：一个命令在 `global_form` 之下运行，当且仅当它不向用户要证明，它的证明也不去上下文的规则集里找 fact；
  它用到的 fact 只有描述它所处理的类型的那些（typedef 的定理、登记的 BNF、datatype 自己的规则）。入选之后，交给它一个依赖上下文的假设的这类 fact，属于不支持的用法，不检查。
  清单以作者定的为准；这句话之下已知的一处出入是 `copy_bnf` 对 quotient 类型走的那条路用到上下文的 simpset（读源码，没有量）。
- **这样的上下文里的 `typedef` 不被支持：只写进文档，代码里不拦**【已定，作者 2026-11-23 05:3x UTC：「我建议 做法二：只写进文档，代码里不拦」「因为 local theory 下的 typedef 本身就不合理」】。
  - 本 feature 因此不碰 `typedef.ML`。stock 的 `typedef` 本来就能写在任何 local theory 里（`local_theory → proof`）；参考手册自己说
    "the newly introduced type constructor cannot depend on parameters or assumptions of the context … The non-emptiness proof may formally depend on local assumptions, but this has little practical relevance"（`HOL_Specific.thy`）。
  - 写了会怎样（8.4A 的 B，实测）：`typedef` 本身成功，存下的定理带着上下文的前提；之后在同一个块里对这个类型写 `copy_bnf` 会失败。
  - concept A1 拟过另一种做法（`Typedef.typedef_cmd` 在开关开着时报错，一处改在 `typedef.ML`，连同一句报错）并一度改进了私有树；作者没有取，已撤回，连同测试。
  - 给用户的话写在 concept 的文档里（A 区计划 2.6"块里别的操作"），不在本 feature 的 README 里：本 feature 只说 `copy_bnf` 的输入若依赖上下文的假设是不支持的用法。

### 8.5 之后要做的

- 状态（2026-11-23 08:0x UTC）：8.4 已由作者定下（见 8.4B），代码与测试已照改，代码评审已通过（见 8.3）；作者 08:0x UTC 下令提交：
  私有树的提交是 `5a9a011`（"global_form: a switch for targets, and six commands that run under it"），本仓库的测试与本文件随后提交。都还没有推送，推送等作者的话。
- 作者定了 8.4 之后改代码与测试；README 的两处（"它没有 Isar 命令""`global_form f` 在 theory target 里与 `f` 相同"）要改写并加上开关与命令的清单，文字要作者批。
- `tools/patched_files.txt`、`tools/signature_additions.txt`（加 `Local_Theory.global_form_enabled`）在发布时更新（SKILL 3.4 第 3 步）。
- 提交、推送按作者的命令。之后建在它上面的 feature 逐级合并：`dot_syntax`（分支头还在本 feature 原来的头 `c105fb8`，是快进）→ `generic_mksimps` → `concept`。
  concept 的 target 在 `setup` 里设这个开关。
