theory Adjustable_References
  imports Main "HOL-Library.Mapping" "HOL-Library.RBT_Mapping"
    "HOL-Library.Code_Target_Numeral"
begin

text \<open>
This is an Isabelle/HOL formalization of ``Adjustable References'', ITP 2013 by Viktor Vafeiadis.
See also \<^url>\<open>https://people.mpi-sws.org/~viktor/arefs/\<close>.
\<close>

datatype ('r, 't) aref = Aref (aref_of: "'r \<Rightarrow> 't") (val_of: 'r)

locale Is_Aref =
  fixes f :: "'r \<Rightarrow> 'a \<Rightarrow> 'b"
  fixes upd :: "'r \<Rightarrow> 'a \<Rightarrow> 'r * 'b"
  assumes "\<forall> x a. f (fst (upd x a)) = f x"
      and "\<forall> x a. snd (upd x a) = f x a"
begin

definition aref_val where
  "aref_val x = Aref f x"

definition aref_get :: "('r, 'a \<Rightarrow> 'b) aref \<Rightarrow> 'a \<Rightarrow> 'b" where
  "aref_get r = f (val_of r)"

lemma get_val:
  "aref_get (aref_val x) = f x"
  unfolding aref_get_def aref_val_def by simp

definition
  "aref_getu = (let a = upd in aref_get)"

lemma aref_getu:
  "aref_getu = aref_get"
  unfolding aref_getu_def Let_def ..

end

text \<open>This axiomatization is necessary for termination proofs\<close>
lemma aref_getu_cong[fundef_cong]:
  "Is_Aref.aref_getu f1 g1 r1 x1 = Is_Aref.aref_getu f1 g2 r2 x2" if
  "\<And> M. g1 M x2 = g2 M x2" "r1 = r2" "x1 = x2"
  sorry

fun fib where
  "fib 0 = (1 :: int)" |
  "fib (Suc 0) = 1" |
  "fib (Suc (Suc n)) = fib (n + 1) + fib n"

definition
  "mem_upd M x \<equiv>
  case Mapping.lookup M x of
    Some v \<Rightarrow> (M, v)
  | None \<Rightarrow> let v = fib x in (Mapping.update x v M, v)
"

definition
  "f M x \<equiv> case Mapping.lookup M x of
    Some v \<Rightarrow> v
  | None \<Rightarrow> fib x
"

code_printing
  constant Is_Aref.aref_val \<rightharpoonup> (SML) "(fn f => fn v => ref v) _ _"

code_printing
  constant Is_Aref.aref_get \<rightharpoonup> (SML) "(fn f => fn r => f (!r)) _ _"

code_printing
  constant Is_Aref.aref_getu \<rightharpoonup> (SML)
    "(fn f => fn u => fn r => fn x => let val (v, fv) = u (!r) x in r := v; fv end) _ _ _"

interpretation Is_Aref f mem_upd
  apply standard
  subgoal
    unfolding f_def mem_upd_def
    apply auto
    apply (intro ext)
    apply (auto split: option.split simp: Let_def)
    subgoal
      by (metis domI domIff lookup_update')
    subgoal
      by (metis lookup_update' option.distinct(1) option.sel)
    subgoal
      by (metis lookup_update_neq option.inject option.simps(3))
    done
  subgoal
    unfolding f_def mem_upd_def
    by (auto split: option.split simp: Let_def)
  done

lemma
  "aref_get (aref_val Mapping.empty) n = fib n"
  unfolding get_val f_def by (auto simp: lookup_empty)

definition
  "fib_memo1 r n = aref_getu r n"

lemma fib_fib_memo:
  "fib n = fib_memo1 (aref_val Mapping.empty) n"
  unfolding get_val f_def fib_memo1_def aref_getu by (auto simp: lookup_empty)

lemma
  "aref_get (aref_val m) n = fib n"
  unfolding get_val f_def oops

definition
  "test n = sum_list (map fib (replicate n 37))"

lemma test_code[code]:
  "test n = (let r = aref_val Mapping.empty in sum_list (map (fib_memo1 r) (replicate n 37)))"
  unfolding test_def fib_fib_memo Let_def ..

code_printing
  constant Is_Aref.aref_val \<rightharpoonup> (SML) "(fn f => fn v => Unsynchronized.ref v) _ _"

code_printing
  constant Is_Aref.aref_get \<rightharpoonup> (SML) "(fn f => fn r => f (!r)) _ _"

code_printing
  constant Is_Aref.aref_getu \<rightharpoonup> (SML)
    "(fn f => fn u => fn r => fn x => let val (v, fv) = u (!r) x in r := v; fv end) _ _ _"

text \<open>This example shows that memoization is actually working.\<close>
(*
code_reflect Test functions test fib nat_of_integer

ML_val \<open>Test.test (Test.nat_of_integer 100000)\<close>
ML_val \<open>Test.fib (Test.nat_of_integer 37)\<close>
*)

paragraph \<open>Experiments for recursive memoization.\<close>

definition
  "fib' = (let r = aref_val Mapping.empty in fib_memo1 r)"

lemma fib'_fib:
  "fib' n = fib n"
  unfolding fib'_def fib_fib_memo Let_def ..

lemma fib_unroll:
  "fib n = (if n = 0 \<or> n = 1 then 1 else fib (n - 1) + fib (n - 2))"
  apply (cases n)
   apply (simp; fail)
  subgoal for m
    by (cases m) auto
  done

lemma fib_code[code]:
  "fib n = (let f = fib' in if n = 0 \<or> n = 1 then 1 else f (n - 1) + f (n - 2))"
  unfolding fib'_fib Let_def by (rule fib_unroll)

export_code fib in SML
export_code fib' checking SML

text \<open>This memoizes nothing.\<close>
(*
code_reflect Test functions fib' nat_of_integer

ML_val \<open>Test.fiba (Test.nat_of_integer 40)\<close>
*)

(* definition "fib2 r n = (if n = 0 \<or> n = 1 then 1 else fib_memo1 r (n - 1) + fib_memo1 r (n - 2))"*)
(*
definition
  "fib2 r n = (if n = 0 \<or> n = 1 then fib_memo1 r n else fib_memo1 r (n - 1) + fib_memo1 r (n - 2))"

lemma fib2_fib:
  "fib2 (aref_val Mapping.empty) n = fib n"
  unfolding fib2_def fib_fib_memo[symmetric] by (simp add: fib_unroll)

definition
  "fib_iter2 n = (let r = aref_val Mapping.empty; _ = map (fib2 r) [0..<n] in fib2 r n)"

lemma fib_iter2_correct:
  "fib_iter2 n = fib n"
  unfolding fib_iter2_def Let_def by (subst fib2_fib; rule HOL.refl)

export_code fib_iter2 in SML
code_reflect Test functions fib_iter2 nat_of_integer
text \<open>Does not memoize\<close>
ML_val \<open>Test.fib_iter2 (Test.nat_of_integer 38)\<close>
*)

context
  fixes r ::  "((nat, int) mapping, nat \<Rightarrow> int) aref"
begin

function fib1 and mem_upd' where
"fib1 n =
  (if n = 0 \<or> n = 1 then 1 else Is_Aref.aref_getu f mem_upd' r (n - 1) + Is_Aref.aref_getu f mem_upd' r (n - 2))"
| "mem_upd' M x = (
  case Mapping.lookup M x of
    Some v \<Rightarrow> (M, v)
  | None \<Rightarrow> let v = fib1 x in (Mapping.update x v M, v))"
     apply auto
  subgoal for P x
    apply (cases x)
     apply auto
    done
  done

lemma wf_term:
  "wf {(x, y). case (x, y) of
    (Inl (n :: nat), Inl m) \<Rightarrow> False
  | (Inl n, Inr (_, m :: nat)) \<Rightarrow> n \<le> m
  | (Inr (_, n), Inl m) \<Rightarrow> n < m
  | (Inr (_, n), Inr (_, m)) \<Rightarrow> False
  }"
proof (rule wfI_min, goal_cases)
  case (1 x Q)
  let ?l = "Inf {n. Inl n \<in> Q}"
  let ?r = "Inf {n. \<exists> M. Inr (M, n) \<in> Q}"
  from \<open>x \<in> Q\<close> consider
    (r)    "{n. Inl n \<in> Q} = {}" "{n. \<exists> M. Inr (M, n) \<in> Q} \<noteq> {}"
    | (l)    "{n. Inl n \<in> Q} \<noteq> {}" "{n. \<exists> M. Inr (M, n) \<in> Q} = {}"
    | (both) "{n. Inl n \<in> Q} \<noteq> {}" "{n. \<exists> M. Inr (M, n) \<in> Q} \<noteq> {}"
    by (cases x) auto
  then show ?case
  proof cases
    case r
    then obtain n2 M where *:
      "Inr (M, n2) \<in> Q"
      by auto
    then obtain M' where "Inr (M'::'a, ?r) \<in> Q"
      by (smt Inf_nat_def LeastI_ex mem_Collect_eq)
    with * \<open>_ = {}\<close> show ?thesis
      by (intro bexI[where x = "Inr (M'::'a, ?r)"]) (auto split: sum.split_asm)
  next
    case l
    then obtain n1 where *:
      "Inl n1 \<in> Q"
      by auto
    with \<open>_ = {}\<close> show ?thesis
      by (intro bexI[where x = "Inl ?l"]) (auto elim: LeastI simp: Inf_nat_def split: sum.split_asm)
  next
    case both
    then obtain n1 n2 M where *:
      "Inl n1 \<in> Q" "Inr (M, n2) \<in> Q"
      by auto
    from this(2) obtain M' where M: "Inr (M'::'a, ?r) \<in> Q"
      by (smt Inf_nat_def LeastI_ex mem_Collect_eq)
    let ?z = "if ?r < ?l then Inr (M'::'a, ?r) else Inl ?l"
    from * M show ?thesis
      apply -
      apply (rule bexI[where x = ?z])
      subgoal
        apply (auto split: sum.split_asm)
        subgoal for m
          by (subgoal_tac "?l \<le> m"; fastforce intro: cInf_lower)
        subgoal for M m
          by (subgoal_tac "?r \<le> m"; fastforce intro: cInf_lower)
        done
      by (auto elim: LeastI simp: Inf_nat_def)
  qed
qed

termination
  by (standard, rule wf_term, auto)

context
  assumes "r = aref_val Mapping.empty"
begin

lemma
  fib1: "fib1 n = fib n" and mem_upd': "mem_upd' M x = mem_upd M x"
proof (induction rule: fib1_mem_upd'.induct)
  case prems: (1 n)
  show ?case
    apply (auto simp del: mem_upd'.simps simp add: Let_def)
    apply (cases n)
     apply simp
    subgoal for m
      apply (cases m)
       apply simp
      using prems apply (simp add: aref_getu_cong[of mem_upd', OF _ HOL.refl HOL.refl])
      unfolding fib_memo1_def[symmetric] \<open>r = _\<close> fib_fib_memo ..
    done
next
  case (2 M x)
  then show ?case
    by (auto simp: Let_def mem_upd_def split: if_split_asm option.split)
qed

end

end

lemma [code]:
  "fib n = fib1 (aref_val Mapping.empty) n"
  by (subst fib1; standard)

definition
  "fib_iter n \<equiv> let _ = map fib [2..<n] in fib n"

definition
  "fib_iter1 n = (let r = aref_val Mapping.empty; _ = map (fib1 r) [2..<n] in fib1 r n)"

lemma fib_iter1_correct:
  "fib_iter1 n = fib n"
  unfolding fib_iter1_def Let_def by (subst fib1; rule HOL.refl)

export_code fib fib_iter in SML
export_code fib checking SML

code_reflect Test functions fib_iter1 fib_iter fib nat_of_integer

text \<open>Also doesn't memoize anything\<close>
ML_val \<open>Test.fib (Test.nat_of_integer 30)\<close>
ML_val \<open>Test.fib_iter (Test.nat_of_integer 30)\<close>

text \<open>This memoizes\<close>
ML_val \<open>Test.fib_iter1 (Test.nat_of_integer 2000)\<close>

end