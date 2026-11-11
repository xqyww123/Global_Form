# global_form：计划（rev 4，2026-11-11，已实现；与代码同步）

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
