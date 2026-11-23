(*  Title:      Global_Form_Test.thy

Checks of Local_Theory.global_form and of the commands that run under it.  Any failing check
fails the build.
*)

theory Global_Form_Test
  imports Main
  keywords "global_form_enable" :: thy_decl
begin

ML \<open>
fun note name ths = Local_Theory.note ((Binding.name name, []), ths) #> snd;

fun define name rhs =
  Local_Theory.define ((Binding.name name, NoSyn), ((Binding.name (name ^ "_def"), []), rhs))
  #>> #1;

(*assumptions and prems of the top context and of the main target*)
fun tables lthy =
  [lthy, Local_Theory.target_of lthy] |> map (fn ctxt =>
    (map Thm.term_of (Assumption.all_assms_of ctxt),
      map Thm.prop_of (Assumption.all_prems_of ctxt)));

fun count_assms ctxt = length (Assumption.all_assms_of ctxt);

(*each prem assumes its assumption, in the same order*)
fun prems_match ctxt =
  eq_list (op aconv)
    (maps Thm.hyps_of (Assumption.all_prems_of ctxt),
      map Thm.term_of (Assumption.all_assms_of ctxt));

fun expect_failure text (run: unit -> unit) =
  let
    val failure =
      (run (); NONE) handle
        ERROR msg => SOME msg
      | THM (msg, _, _) => SOME msg
      | Fail msg => SOME msg;
  in
    (case failure of
      NONE => error ("No failure, expected: " ^ text)
    | SOME msg =>
        if String.isSubstring text msg then ()
        else error ("Expected: " ^ text ^ "\nbut got: " ^ msg))
  end;

fun has_const c = Term.exists_Const (fn (c', _) => c' = c);
fun prem_has_const c th = exists (has_const c) (Thm.prems_of th);
fun has_free t = Term.exists_subterm Term.is_Free t;

(*a target enables Local_Theory.global_form for itself; here it is enabled at every level of the
  local theory that is open, by a test-only command*)
val global_form_enable =
  Local_Theory.map_contexts (K (Config.put Local_Theory.global_form_enabled true));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>global_form_enable\<close>
    "enable Local_Theory.global_form in the open local theory"
    (Scan.succeed global_form_enable);
\<close>


section \<open>Theory target: no effect (test 1)\<close>

local_setup \<open>global_form_enable #> Local_Theory.global_form (note "t1" @{thms refl})\<close>
local_setup \<open>note "t1_plain" @{thms refl}\<close>

ML \<open>\<^assert> (Thm.prop_of @{thm t1} aconv Thm.prop_of @{thm t1_plain})\<close>


section \<open>Not a local theory (test 13)\<close>

ML \<open>
expect_failure "Missing local theory context" (fn () =>
  ignore (Local_Theory.global_form I \<^context>))
\<close>


section \<open>A stock locale\<close>

locale L =
  fixes S :: "'a set"
  assumes ne: "S \<noteq> {}"

context L
begin

text \<open>Test 16: where it is not enabled, global_form does nothing.\<close>

local_setup \<open>Local_Theory.global_form (fn lthy =>
  (\<^assert> (count_assms lthy = 1); note "off" @{thms refl [of S]} lthy))\<close>

global_form_enable

text \<open>Test 2: a result that does not use the assumption.\<close>

local_setup \<open>Local_Theory.global_form (note "b" @{thms refl [of S]})\<close>

lemma uses_b: "S = S" by (rule b)

text \<open>Test 3: a result that uses the assumption is an error.\<close>

local_setup \<open>fn lthy =>
  (expect_failure "variable free in assumptions" (fn () =>
    ignore (Local_Theory.global_form (note "c" @{thms ne}) lthy)); lthy)\<close>

text \<open>Test 4: the assumptions are absent inside and back afterwards.\<close>

local_setup \<open>fn lthy =>
  let
    val before = tables lthy;
    val _ = \<^assert> (count_assms lthy = 1);
    val lthy' = lthy |> Local_Theory.global_form (fn lthy1 =>
      (\<^assert> (count_assms lthy1 = 0);
       \<^assert> (null (Assumption.all_prems_of lthy1));
       \<^assert> (count_assms (Local_Theory.target_of lthy1) = 0);
       note "b4" @{thms refl [of S]} lthy1));
    val _ = \<^assert> (tables lthy' = before);
  in lthy' end\<close>

lemma d: "S \<noteq> {} \<or> S = {}" using ne by simp

text \<open>Test 5 (ii): a definition made in the same operation stays.\<close>

local_setup \<open>fn lthy =>
  let val (c, lthy1) = define "c" \<^term>\<open>S \<union> S\<close> lthy in
    lthy1 |> Local_Theory.global_form (fn lthy2 =>
      (\<^assert> (count_assms lthy2 = 1);
       note "f" [Thm.reflexive (Thm.cterm_of lthy2 c)] lthy2))
  end\<close>

text \<open>Test 6: a definition inside stays on top of the assumptions put back.\<close>

local_setup \<open>fn lthy =>
  let
    val (g, lthy') = lthy |> Local_Theory.global_form_result (fn lthy1 =>
      let val (g, lthy2) = define "g" \<^term>\<open>S \<union> S\<close> lthy1
      in (g, note "h" [Thm.reflexive (Thm.cterm_of lthy2 g)] lthy2) end);
    val _ = \<^assert> (count_assms lthy' = 2);
    val _ = \<^assert> (prems_match lthy');
  in note "h2" [Thm.reflexive (Thm.cterm_of lthy' g)] lthy' end\<close>

text \<open>Test 7: nested levels opened and closed inside, with a definition entry on top before.\<close>

local_setup \<open>fn lthy0 =>
  let
    val (_, lthy) = define "c7" \<^term>\<open>S \<union> S\<close> lthy0;
    fun nested lthy1 =
      lthy1
      |> Local_Theory.begin_nested |> #2
      |> note "n7" @{thms refl [of S]}
      |> Local_Theory.end_nested;
    val plain = nested lthy;
    val wrapped = lthy |> Local_Theory.global_form (fn lthy1 =>
      (\<^assert> (count_assms lthy1 = 1); nested lthy1));
    val _ = \<^assert> (tables wrapped = tables plain);
    val _ = \<^assert> (count_assms (Local_Theory.target_of wrapped) = 1);
  in wrapped end\<close>

text \<open>Test 9: nested use.\<close>

local_setup \<open>fn lthy =>
  let
    val lthy' = lthy |> Local_Theory.global_form (fn lthy1 =>
      let
        val lthy2 = Local_Theory.global_form (note "n9" @{thms refl [of S]}) lthy1;
        val _ = \<^assert> (count_assms lthy2 = 0);
        val _ = expect_failure "variable free in assumptions" (fn () =>
          ignore (note "c9" @{thms ne} lthy2));
      in lthy2 end);
    val _ = \<^assert> (count_assms lthy' = 1);
  in lthy' end\<close>

text \<open>Tests 10 and 11: Goal.future_result packs no assumption.\<close>

local_setup \<open>fn lthy =>
  let
    val _ = lthy |> Local_Theory.global_form (fn lthy1 =>
      let
        val prop = \<^prop>\<open>S = S\<close>;
        val th = Goal.future_result lthy1 (Future.value @{thm refl [of S]}) prop;
        val _ = Thm.consolidate [th];
        val _ = \<^assert> (null (Thm.hyps_of th) andalso Thm.prop_of th aconv prop);
        val _ = expect_failure "forall_intr" (fn () =>
          Thm.consolidate
            [Goal.future_result lthy1 (Future.value @{thm ne}) \<^prop>\<open>S \<noteq> {}\<close>]);
      in lthy1 end);
  in lthy end\<close>

text \<open>Test 12: a result with the hypothesis that leaves unnoted is an ordinary local theorem.\<close>

local_setup \<open>fn lthy =>
  let val (th, lthy') = Local_Theory.global_form_result (pair @{thm ne}) lthy
  in note "m" [th] lthy' end\<close>

text \<open>Test 8: a nested context with an assumption and a definition.\<close>

context
  fixes y :: 'a and d :: "'a set"
  assumes py: "y \<in> S"
  defines "d \<equiv> {y}"
begin

local_setup \<open>fn lthy =>
  let
    val before = tables lthy;
    val _ = \<^assert> (count_assms lthy = 3);
    val lthy' = lthy |> Local_Theory.global_form (fn lthy1 =>
      (\<^assert> (count_assms lthy1 = 1);
       \<^assert> (prems_match lthy1);
       \<^assert> (count_assms (Local_Theory.target_of lthy1) = 0);
       note "k" @{thms refl [of d]} lthy1));
    val _ = \<^assert> (tables lthy' = before);
  in lthy' end\<close>

end

end

ML \<open>
val no_prems = null o Thm.prems_of;

(*test 16*)
val _ = \<^assert> (prem_has_const \<^const_name>\<open>L\<close> @{thm L.off});
(*test 2*)
val _ = \<^assert> (no_prems @{thm L.b});
(*test 4*)
val _ = \<^assert> (no_prems @{thm L.b4});
val _ = \<^assert> (prem_has_const \<^const_name>\<open>L\<close> @{thm L.d});
(*test 5 (ii)*)
val _ = \<^assert> (no_prems @{thm L.f});
val _ = \<^assert> (has_const \<^const_name>\<open>L.c\<close> (Thm.prop_of @{thm L.f}));
val _ = \<^assert> (not (has_free (Thm.prop_of @{thm L.f})));
(*test 6*)
val _ = \<^assert> (no_prems @{thm L.h});
val _ = \<^assert> (has_const \<^const_name>\<open>L.g\<close> (Thm.prop_of @{thm L.h}));
val h2 = Thm.prop_of @{thm L.h2};
val _ = \<^assert> (prem_has_const \<^const_name>\<open>L\<close> @{thm L.h2});
val _ = \<^assert> (has_const \<^const_name>\<open>L.g\<close> h2);
val _ = \<^assert> (not (has_free h2));
val _ = \<^assert> (map #1 (Term.add_var_names h2 []) = ["S"]);
(*test 8*)
val _ = \<^assert> (no_prems @{thm L.k});
val _ = \<^assert> (has_const \<^const_name>\<open>insert\<close> (Thm.prop_of @{thm L.k}));
val _ = \<^assert> (not (has_free (Thm.prop_of @{thm L.k})));
val _ = \<^assert> (map #1 (Term.add_var_names (Thm.prop_of @{thm L.k}) []) = ["y"]);
(*test 12*)
val _ = \<^assert> (prem_has_const \<^const_name>\<open>L\<close> @{thm L.m});
\<close>

text \<open>Test 2, continued: the fact is there when the locale is opened again and in an
  interpretation.\<close>

context L
begin

lemma "S = S" by (rule b)

end

interpretation I: L "{0::nat}" by standard simp

lemma "{0::nat} = {0}" by (rule I.b)


section \<open>A locale with a definition (test 5 (i))\<close>

locale LD =
  fixes S :: "'a set" and D :: "'a set"
  assumes ne: "S \<noteq> {}"
  defines "D \<equiv> S \<union> S"

context LD
begin

global_form_enable

local_setup \<open>fn lthy =>
  let val before = tables lthy in
    lthy
    |> Local_Theory.global_form (fn lthy1 =>
        (\<^assert> (count_assms lthy1 = 1);
         \<^assert> (prems_match lthy1);
         note "e" @{thms refl [of D]} lthy1))
    |> tap (fn lthy' => \<^assert> (tables lthy' = before))
  end\<close>

end

ML \<open>
val e = Thm.prop_of @{thm LD.e};
val _ = \<^assert> (no_prems @{thm LD.e});
val _ = \<^assert> (not (has_free e));
val _ = \<^assert> (has_const \<^const_name>\<open>sup\<close> e);
val _ = \<^assert> (map #1 (Term.add_var_names e []) = ["S"]);
\<close>


section \<open>A hypothesis without fixed variables (test 15)\<close>

context
  assumes Q: "\<forall>x::nat. x = x"
begin

global_form_enable

local_setup \<open>fn lthy =>
  (expect_failure "Undeclared hyps" (fn () =>
    ignore (Local_Theory.global_form (note "q1" @{thms Q}) lthy));
   expect_failure "Undeclared hyps" (fn () =>
    ignore (Local_Theory.global_form
      (Local_Theory.note (Binding.empty_atts, @{thms Q}) #> #2) lthy));
   lthy)\<close>

end


section \<open>The commands that run under global_form, in a locale (tests 14, 17 to 22)\<close>

locale LT =
  fixes S :: "'a set"
  assumes ne: "S \<noteq> {}"

typedef 'b outside = "UNIV :: 'b set" by simp
typedef 'b outside0 = "UNIV :: 'b set" by simp

text \<open>Where global_form is not enabled the commands are the stock ones: for comparison.\<close>

context LT
begin

datatype 'b ls0 = LNil0 | LCons0 'b "'b ls0"
datatype 'b tr0 = Leaf0 | Node0 'b "'b tr0 list"
codatatype 'b strm0 = SCons0 (shd0: 'b) (stl0: "'b strm0")
definition pick0 :: "'b \<Rightarrow> 'b \<times> 'a set" where "pick0 x = (x, S)"
primrec len0 :: "'b ls0 \<Rightarrow> nat" where "len0 LNil0 = 0" | "len0 (LCons0 x xs) = Suc (len0 xs)"
copy_bnf 'b outside0

ML \<open>
val _ = \<^assert> (not (null (Thm.hyps_of @{thm ls0.induct})));
val _ = \<^assert> (not (null (Thm.hyps_of @{thm strm0.coinduct})));
val _ = \<^assert> (not (null (Thm.hyps_of @{thm tr0.induct})));
\<close>

end

context LT
begin

global_form_enable

text \<open>Test 14: datatype and codatatype.\<close>

datatype 'b ls = LNil | LCons 'b "'b ls"
datatype 'b tr = Leaf | Node 'b "'b tr list"
codatatype 'b strm = SCons (shd: 'b) (stl: "'b strm")

ML \<open>
val _ = \<^assert> (null (Thm.hyps_of @{thm ls.induct}));
val _ = \<^assert> (null (Thm.hyps_of @{thm tr.induct}));
val _ = \<^assert> (null (Thm.hyps_of @{thm tr.exhaust}));
val _ = \<^assert> (null (Thm.hyps_of @{thm strm.coinduct}));
\<close>

text \<open>Test 17: definition, also of a constant that depends on the parameter of the locale, with
  an attribute, and with a condition.\<close>

definition pick :: "'b \<Rightarrow> 'b \<times> 'a set" where "pick x = (x, S)"
definition plain_def [simp]: "plain = (0::nat)"
definition cond :: "nat \<Rightarrow> 'a set" where "cond n = S" if "n > 0"

lemma uses_plain: "plain + 0 = 0" by simp

text \<open>For comparison the ML function, which is not under global_form.\<close>

local_setup \<open>fn lthy =>
  Specification.definition {verbose = false} NONE [] []
    (Binding.empty_atts, Syntax.read_prop lthy "pick1 (x::'b) = (x, S)") lthy |> #2\<close>

text \<open>Test 18: primrec, on a datatype of the block, with and without the parameter.\<close>

primrec len :: "'b ls \<Rightarrow> nat" where "len LNil = 0" | "len (LCons x xs) = Suc (len xs)"
primrec tag :: "'b ls \<Rightarrow> 'a set" where "tag LNil = S" | "tag (LCons x xs) = tag xs"

text \<open>Test 19: primcorec is not under global_form (it proves with the rules of the context),
  also for a codatatype that is.\<close>

primcorec same :: "'b \<Rightarrow> 'b strm" where "same x = SCons x (same x)"

text \<open>Test 20: datatype_compat, which notes rules for a datatype that is nested; for comparison
  its ML function, which is not under global_form.  (For a datatype of a block where
  global_form is not enabled the stock command fails.)\<close>

datatype_compat ls
datatype_compat tr

datatype 'b un = ULeaf | UNode 'b "'b un list"
local_setup \<open>BNF_LFP_Compat.datatype_compat_cmd ["un"]\<close>

text \<open>Test 21: copy_bnf, for a type defined outside the block.\<close>

copy_bnf 'b outside

text \<open>Test 22: afterwards the assumption is back.\<close>

lemma after: "S \<noteq> {} \<or> pick x = pick x" using ne by simp

ML \<open>\<^assert> (count_assms \<^context> = 1)\<close>

end

ML \<open>
(*every global fact whose name has the given part, lazy ones forced*)
fun facts_named infix_name =
  Facts.dest_static false [] (Global_Theory.facts_of \<^theory>)
  |> filter (fn (name, _) => String.isSubstring infix_name name)
  |> maps #2;

val with_premise = filter (prem_has_const \<^const_name>\<open>LT\<close>);

fun without_premise n infix_name =
  let val ths = facts_named infix_name
  in \<^assert> (length ths > n andalso null (with_premise ths)) end;

(*test 14*)
val _ = List.app (without_premise 20) [".tr.", ".strm.", ".ls."];
val _ = \<^assert> (not (null (with_premise (facts_named ".ls0."))));
val _ = \<^assert> (not (null (with_premise (facts_named ".tr0."))));
val _ = \<^assert> (not (null (with_premise (facts_named ".strm0."))));
(*test 17*)
val _ = \<^assert> (no_prems @{thm LT.pick_def});
val _ = \<^assert> (map #1 (Term.add_var_names (Thm.prop_of @{thm LT.pick_def}) []) = ["x", "S"]);
val _ = \<^assert> (no_prems @{thm LT.plain_def});
val _ = \<^assert> (Thm.nprems_of @{thm LT.cond_def} = 1);
val _ = \<^assert> (not (prem_has_const \<^const_name>\<open>LT\<close> @{thm LT.cond_def}));
val _ = \<^assert> (prem_has_const \<^const_name>\<open>LT\<close> @{thm LT.pick0_def});
val _ = \<^assert> (prem_has_const \<^const_name>\<open>LT\<close> @{thm LT.pick1_def});
val _ = \<^assert> (prem_has_const \<^const_name>\<open>LT\<close> @{thm LT.uses_plain});
(*test 18*)
val _ = List.app (without_premise 0) [".len.", ".tag."];
val _ = \<^assert> (has_const \<^const_name>\<open>LT.tag\<close> (Thm.prop_of (hd @{thms LT.tag.simps})));
val _ = \<^assert> (not (null (with_premise (facts_named ".len0."))));
(*test 19*)
val _ = \<^assert> (not (null (with_premise (facts_named ".same."))));
(*test 20*)
val _ = without_premise 2 ".compat_tr.";
val _ = \<^assert> (not (null (with_premise (facts_named ".compat_un."))));
(*test 21*)
val _ = without_premise 50 ".outside.";
val _ = \<^assert> (not (null (with_premise (facts_named ".outside0."))));
(*test 22*)
val _ = \<^assert> (prem_has_const \<^const_name>\<open>LT\<close> @{thm LT.after});
\<close>

context LT
begin

lemma "t = Leaf \<or> (\<exists>x ts. t = Node x ts)" by (cases t) auto

lemma "s = SCons (shd s) (stl s)" by simp

lemma "len (LCons x LNil) = Suc 0" by simp

lemma "fst (pick x) = x" by (simp add: pick_def)

end

interpretation J: LT "{0::nat}" by standard simp

lemma "J.len (J.LCons x J.LNil) = Suc 0" by simp

end
