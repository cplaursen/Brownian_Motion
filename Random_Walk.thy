theory Random_Walk
  imports Markov_Semigroup Stochastic_Process
begin

lemma integrable_scale_measure:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, second_countable_topology}"
  assumes "integrable M f"
  shows "integrable (scale_measure (ennreal n) M) f"
  using assms apply (auto simp add: integrable_iff_bounded nn_integral_scale_measure)
  using ennreal_less_top ennreal_mult_less_top by blast

lemma integral_scale_measure:
  fixes f :: "'a \<Rightarrow> 'b :: {banach, second_countable_topology}"
  assumes "integrable M f" "n \<ge> 0"
  shows "integral\<^sup>L (scale_measure (ennreal n) M) f = n *\<^sub>R integral\<^sup>L M f"
  using assms
proof induction
  case (base A c)
  then show ?case
    by (auto simp: measure_def enn2real_mult integrable_scale_measure)
next
  case (add f g)
  then show ?case
    by (auto simp: integrable_scale_measure field_simps)
next
  case (lim f s)
  then show ?case
  proof (intro LIMSEQ_unique)
    show "(\<lambda>i. integral\<^sup>L (scale_measure (ennreal n) M) (s i)) \<longlonglongrightarrow> integral\<^sup>L (scale_measure (ennreal n) M) f"
      apply (rule integral_dominated_convergence[where w="(\<lambda>x. 2 * norm (f x))"])
      using lim apply (auto simp: integrable_scale_measure)
      using space_scale_measure apply fastforce+
      done
    show "(\<lambda>i. integral\<^sup>L (scale_measure (ennreal n) M) (s i)) \<longlonglongrightarrow> n *\<^sub>R integral\<^sup>L M f"
      apply (subst lim(5)[OF lim(6)])
      apply (intro tendsto_scaleR)
       apply simp
      apply (rule integral_dominated_convergence[where w="(\<lambda>x. 2 * norm (f x))"])
      using lim by auto
  qed
qed

(*
lemma nn_integral_scale_measure:
  fixes f :: "'a \<Rightarrow> ennreal"
  assumes "f \<in> borel_measurable M" "n \<ge> 0" "AE x in M. 0 \<le> f x"
  shows "integral\<^sup>N (scale_measure (ennreal n) M) f = n * integral\<^sup>N M f"
*)

lemma "x ## to_stream f = to_stream (\<lambda> i. if i = 0 then x else f (i - 1))"
proof -
  have "case_nat = (\<lambda>a f n. if n = 0 then a::'a else f (n - 1))"
    by (metis (no_types) Nitpick.case_nat_unfold)
  then show ?thesis
    by (metis (no_types) to_stream_nat_case)
qed

lemma PiM_iter':
  assumes "sequence_space M" "pair_sigma_finite (Pi\<^sub>M UNIV (\<lambda>i::nat. M)) M"
  shows "distr ((\<Pi>\<^sub>M i::nat\<in>UNIV. M) \<Otimes>\<^sub>M M) (\<Pi>\<^sub>M i::nat\<in>UNIV. M) (\<lambda> (x, y). case_nat y x) = (\<Pi>\<^sub>M i::nat\<in>UNIV. M)" (is "?lhs = ?rhs")
using assms
proof -
  have "?lhs
       = distr (distr (M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>i. M)) (Pi\<^sub>M UNIV (\<lambda>i. M) \<Otimes>\<^sub>M M) (\<lambda>(x, y). (y, x))) (Pi\<^sub>M UNIV (\<lambda>i. M)) (\<lambda>(x, y). case_nat y x)"
    using assms(2) pair_sigma_finite.distr_pair_swap by fastforce
  also have "... = distr (M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>i. M)) (Pi\<^sub>M UNIV (\<lambda>i. M)) ((\<lambda>(x, y). case_nat y x) \<circ> (\<lambda>(x, y). (y, x)))"
    by (simp add: distr_distr)
  also have "... = distr (M \<Otimes>\<^sub>M Pi\<^sub>M UNIV (\<lambda>i. M)) (Pi\<^sub>M UNIV (\<lambda>i. M)) ((\<lambda>(x, y). case_nat x y))"
    by (simp add: comp_def split_def)
  also have "... = ?rhs"
    using assms(1) sequence_space.PiM_iter by blast
  finally show ?thesis .
qed


lemma stream_space_eq_distr_prod:
  assumes "sequence_space M" "pair_sigma_finite (Pi\<^sub>M UNIV (\<lambda>i::nat. M)) M"
  shows "stream_space M = distr ((Pi\<^sub>M UNIV (\<lambda>i. M)) \<Otimes>\<^sub>M M) (stream_space M) (\<lambda> X. to_stream ((\<lambda>(\<omega>, s). case_nat s \<omega>) X))" (is "?lhs = ?rhs")
proof -
  have "?rhs = distr ((Pi\<^sub>M UNIV (\<lambda>i. M)) \<Otimes>\<^sub>M M) (stream_space M) (to_stream \<circ> (\<lambda>(\<omega>, s). case_nat s \<omega>))"
    by (metis o_apply)
  also have "... = distr (distr (Pi\<^sub>M UNIV (\<lambda>i. M) \<Otimes>\<^sub>M M) (Pi\<^sub>M UNIV (\<lambda>i. M)) (\<lambda>(\<omega>, s). case_nat s \<omega>)) (stream_space M) to_stream"
    by (simp add: distr_distr)
  also have "... = distr (Pi\<^sub>M UNIV (\<lambda>i. M)) (stream_space M) to_stream"
    by (simp add: PiM_iter' assms(1) assms(2))
  also have "... = ?lhs"
    by (metis stream_space_eq_distr)
  finally show ?thesis ..
qed

lemma (in prob_space) integral_stream_space:
  fixes f :: "'a stream \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable (stream_space M) f"
  shows "(\<integral>X. f X \<partial>stream_space M) = \<integral>x. (\<integral>X. f (x ## X) \<partial>stream_space M) \<partial>M"
proof -
  interpret S: sequence_space M ..
  interpret P: pair_sigma_finite M "\<Pi>\<^sub>M i::nat\<in>UNIV. M" ..

  have "sequence_space M"
    using S.sequence_space_axioms by fastforce

  have "pair_sigma_finite M (\<Pi>\<^sub>M i::nat\<in>UNIV. M)"
    using P.pair_sigma_finite_axioms by force

  have 1:"(\<lambda>X. to_stream (case X of (\<omega>, s) \<Rightarrow> case_nat s \<omega>)) = (\<lambda>(x, y). (y ## to_stream x))"
    using to_stream_nat_case by fastforce

  have ss: "stream_space M = distr (Pi\<^sub>M UNIV (\<lambda>i. M) \<Otimes>\<^sub>M M) (stream_space M) (\<lambda>(x, y). (y ## to_stream x))"
    using S.sequence_space_axioms P.pair_sigma_finite_axioms apply (subst stream_space_eq_distr_prod)
    apply simp
     apply (simp add: pair_sigma_finite_def)
    apply (simp add:1)
    done

  have "integrable (distr (Pi\<^sub>M UNIV (\<lambda>i. M) \<Otimes>\<^sub>M M) (stream_space M) (\<lambda>(x, y). y ## to_stream x)) f"
    using assms ss by presburger

  hence 2: "integrable (Pi\<^sub>M UNIV (\<lambda>i. M) \<Otimes>\<^sub>M M) (\<lambda>x. f (case x of (x, y) \<Rightarrow> y ## to_stream x))"
    by (rule_tac integrable_distr[where T="\<lambda>(x, y). y ## to_stream x" and f=f and M'="stream_space M"], simp_all)

  hence 3:"integrable (Pi\<^sub>M UNIV (\<lambda>i. M) \<Otimes>\<^sub>M M) (\<lambda>(x, y). f (y ## to_stream x))"
    by (simp add: prod.case_eq_if split_def)

  have "(\<integral>X. f X \<partial>stream_space M) = (\<integral>X. f (to_stream X) \<partial>S.S)"
    using assms by (subst stream_space_eq_distr) (simp add: integral_distr)
  also have "\<dots> = (\<integral>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X)) \<partial>(M \<Otimes>\<^sub>M S.S))"
    using assms by (subst S.PiM_iter[symmetric]) (simp add: integral_distr)
  also have "\<dots> = (\<integral>x. \<integral>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) (x, X))) \<partial>S.S \<partial>M)"
    apply (subst P.integral_fst')
    using assms apply auto
    apply (subst P.integrable_product_swap_iff[symmetric])
    apply (simp add: to_stream_nat_case 3)
    done
  also have "\<dots> = (\<integral>x. \<integral>X. f (x ## to_stream X) \<partial>S.S \<partial>M)"
    by (auto simp: to_stream_nat_case)
  also have "\<dots> = (\<integral>x. \<integral>X. f (x ## X) \<partial>stream_space M \<partial>M)"
    using assms apply (subst stream_space_eq_distr)
    by (simp add: integral_distr cong: Bochner_Integration.integral_cong)
  finally show ?thesis .
qed

section \<open> Probability measure on booleans \<close>
definition bool_measure :: "bool measure" where
"bool_measure \<equiv> scale_measure (ennreal (1/2)) (count_space UNIV)"

lemma space_bool_measure[simp]: "space bool_measure = UNIV"
  unfolding bool_measure_def using space_scale_measure by fastforce

lemma sets_bool_measure[simp]: "sets bool_measure = Pow UNIV"
  unfolding bool_measure_def using sets_scale_measure by simp

interpretation bool_space: prob_space bool_measure
  unfolding bool_measure_def apply (intro prob_spaceI)
  apply (simp add: space_scale_measure)
  by (metis divide_ennreal_def ennreal_divide_self 
      ennreal_less_top ennreal_numeral mult.commute zero_neq_numeral)

lemma bool_prob_True: "bool_space.prob {True} = 1/2"
  unfolding bool_measure_def
  by (simp only: measure_scale_measure, simp)

lemma bool_prob_False: "bool_space.prob {False} = 1/2"
  unfolding bool_measure_def
  by (simp only: measure_scale_measure, simp)

lemma integrable_bool_measure[simp]:
 "integrable bool_measure (f :: bool \<Rightarrow> 'a::{second_countable_topology, banach})"
  unfolding bool_measure_def
  apply (rule integrable_scale_measure)
  by (simp add: integrable_count_space)

lemma integral_bool_measure: 
  fixes f:: "bool \<Rightarrow> real"
  shows "(\<integral>\<omega>. f \<omega> \<partial>bool_measure) = (f True + f False) / 2"
  unfolding bool_measure_def
  apply (subst integral_scale_measure)
    apply (auto simp: integrable_count_space)
  by (simp add: UNIV_bool infsetsum_def[symmetric])

lemma integral_pos_bool_measure: 
  fixes f:: "bool \<Rightarrow> ennreal"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>bool_measure) = (f True + f False) / 2"
  unfolding bool_measure_def
  apply (subst integral_scale_measure)
    apply (auto simp: integrable_count_space)
  by (simp add: UNIV_bool infsetsum_def[symmetric])


section \<open> Random walk \<close>
interpretation bool_prod: product_prob_space "(\<lambda>_. bool_measure)" UNIV
  by (simp add: bool_space.prob_space_axioms product_prob_spaceI)

interpretation bool_stream: prob_space "stream_space bool_measure"
  by (fact bool_space.prob_space_stream_space)

definition coin_tosses :: "(nat, bool stream, real) stochastic_process" where
"coin_tosses \<equiv> bool_stream.process_of (sigma UNIV UNIV) UNIV (\<lambda>n \<omega>. if \<omega> !! n then 1 else -1) 0"

lemma measurable_coin_tosses[measurable]: 
  "\<And>n. (\<lambda>\<omega>. if \<omega> !! n then 1 else (-1:: real)) \<in> (stream_space bool_measure) \<rightarrow>\<^sub>M (sigma UNIV UNIV)"
  by (measurable, simp add: measurable_ident_sets sets_stream_space_cong)

lemma coin_tosses_source[simp]: "proc_source coin_tosses = stream_space bool_measure"
  and coin_tosses_target[simp]: "proc_target coin_tosses = sigma UNIV UNIV"
  and coin_tosses_process[simp]: "process coin_tosses = (\<lambda>n \<omega>. if \<omega> !! n then 1 else -1)"
  unfolding coin_tosses_def by simp_all


lemma "distr (Pi\<^sub>M UNIV (\<lambda>i. bool_measure)) (Pi\<^sub>M UNIV (\<lambda>i. sigma UNIV UNIV)) ((\<lambda>x. \<lambda>i\<in>UNIV. if x !! i then 1::real else - 1) \<circ> to_stream) =
    Pi\<^sub>M UNIV (\<lambda>i. distr (Pi\<^sub>M UNIV (\<lambda>i. bool_measure)) (sigma UNIV UNIV) ((\<lambda>\<omega>. if \<omega> !! i then 1 else - 1) \<circ> to_stream))" (is "?lhs = ?rhs")
proof -
  have "?lhs = distr (distr (Pi\<^sub>M UNIV (\<lambda>i. bool_measure)) (stream_space bool_measure) to_stream) (Pi\<^sub>M UNIV (\<lambda>i::nat. sigma UNIV UNIV))
     (\<lambda>x. \<lambda>i\<in>UNIV. if x !! i then 1::real else - (1::real))"
    apply (subst distr_distr[where N="stream_space bool_measure", THEN sym])
      apply simp_all
    apply measurable
    done
  also have "... = distr (stream_space bool_measure) (Pi\<^sub>M UNIV (\<lambda>i::nat. sigma UNIV UNIV)) (\<lambda>x. \<lambda>i\<in>UNIV. if x !! i then 1::real else - (1::real))"
    by (metis stream_space_eq_distr)
  oops

lemma to_stream_snth [simp]: "to_stream f !! i = f i"
  by (simp add: to_stream_def)

lemma to_stream_comp_elim: "(\<lambda>x. \<lambda>i\<in>UNIV. if x !! i then 1 else - 1) \<circ> to_stream = (\<lambda>x. \<lambda>i\<in>UNIV. if x i then 1 else - 1)"
  by (auto simp add: fun_eq_iff)

lemma independent_coin_tosses: "bool_stream.indep_vars (\<lambda>_. sigma UNIV UNIV) (\<lambda>n \<omega>. if \<omega> !! n then 1 else (-1:: real)) UNIV"
  apply (simp add: bool_stream.indep_vars_iff_distr_eq_PiM)
  apply (subst stream_space_eq_distr)
  apply (subst distr_distr)
    apply measurable
    apply (simp add: measurable_ident_sets sets_stream_space_cong)
   apply simp
  apply (simp add: to_stream_comp_elim)
  apply (subst stream_space_eq_distr)
  apply (subst distr_distr)
    apply simp_all
  apply (rule measure_eqI_PiM_infinite)
     defer
     apply simp
    prefer 3
    apply (simp add: sets_PiM_cong)
  sorry

lemma random_walk_measurable[measurable]:
  "bool_stream.random_variable borel (\<lambda>\<omega>. \<Sum>j = 1..n. if \<omega> !! j then (1::real) else -1)"
  by measurable (simp add: measurable_ident_sets sets_stream_space_cong)

definition random_walk :: "(nat, bool stream, real) stochastic_process" where
"random_walk \<equiv> bool_stream.process_of borel UNIV (\<lambda>n \<omega>. \<Sum>j = 1..n. if \<omega> !! j then 1 else -1) 0"

lemma source_random_walk: "proc_source random_walk = stream_space bool_measure"
  and target_random_walk: "proc_target random_walk = borel"
  and process_random_walk: "process random_walk = (\<lambda>n \<omega>. \<Sum>j = 1..n. if \<omega> !! j then 1 else -1)"
  unfolding random_walk_def using random_walk_measurable by simp_all

lemma sum_bound: "abs(\<Sum>j = Suc 0..n. if x !! j then 1 else - 1) \<le> real n"
  by (induct n, simp_all, linarith)

lemma integrable_random_walk [simp]: "integrable (stream_space bool_measure) (process random_walk n)"
  apply (rule bool_stream.integrable_const_bound[where B="n"])
   apply (simp_all add: sum_bound process_random_walk)
  using One_nat_def random_walk_measurable apply presburger
  done

lemma integrable_random_walk_sum [simp]: "integrable (stream_space bool_measure) (\<lambda>x. if stl x !! n then 1::real else - 1)"
  apply (rule bool_stream.integrable_const_bound[where B="1"])
   apply simp_all
  apply measurable
  apply (simp add: measurable_ident_sets sets_stream_space_cong)
  done

find_theorems "distributed (stream_space ?M)" lborel

find_theorems "integral\<^sup>L (stream_space ?M)"

term "integral\<^sup>L (stream_space bool_measure)"

find_theorems "bool_stream.expectation"

find_theorems integrable stream_space

find_theorems "distr (stream_space ?M)"

find_theorems stream_space std_normal_distribution

find_theorems bool_space.prob

find_theorems measure scale_measure


lemma "bool_stream.expectation (\<lambda>X. if X !! n then 1::real else - 1) = 0"
  find_theorems bool_stream.expectation
  apply (rule bool_stream.standard_normal_distributed_expectation)
  apply (simp add: distributed_def)
  apply auto
  apply (induct n)
    apply simp
  oops

  find_theorems lebesgue_integral If

  thm Bochner_Integration.integral_add

  term of_bool

  term indicator
            
  find_theorems "distr (stream_space ?M) ?f ?X = ?K"

  find_theorems If indicator

lemma If_indicator: "(\<lambda>x. if P x then f x :: 'a::real_vector else g x) = (\<lambda>x. indicator {x. P x} x *\<^sub>R f x + indicator {x. \<not>P x} x *\<^sub>R g x)"
  by (auto)

find_theorems integrable indicator

find_theorems "integral\<^sup>L" "indicator"

(*
lemma "A \<in> sets M \<Longrightarrow> integral\<^sup>L (\<lambda> x. indicator A x *\<^sub>R f x \<partial>M) = \<integral>\<^sup>L x\<in>A. f x \<partial>M"
*)

find_theorems bool_stream.indep_set


term "prob_space.indep_vars"


find_theorems "bool_stream.prob" "bool_stream.indep_vars"

term case_bool

lemma "space (stream_space bool_measure) = UNIV"
  by (simp add: space_stream_space)

term

thm prob_space.prob_stream_space

thm bool_stream.prob_stream_space

find_theorems "integral\<^sup>L" bool_measure


find_theorems bool_stream.prob

lemma "(emeasure (stream_space bool_measure) {x\<in>space (stream_space bool_measure). shd x}) = ennreal 0.5"
  thm bool_space.emeasure_stream_space
  apply (subst bool_space.emeasure_stream_space)
   apply measurable
   defer
  apply simp
  thm bool_stream.nn_integral_stream_space
  
  apply (subst bool_stream.nn_integral_stream_space)
  oops

  term sum

lemma PiE_Collect: "PiE A B = {f. (\<forall> x\<in>A. f x \<in> B x) \<and> (\<forall> x\<in>-A. f x = undefined)}"
  by auto

term "(\<lambda> f. sum f C) ` PiE A B"

find_theorems sum PiE

lemma sum_as_sum_list: "sum f {0..n} = sum_list (map f [0..<n+1])"
  by (metis atLeastAtMost_upt distinct_upt semiring_norm(174) sum_list_distinct_conv_sum_set)

lemma f1: "(\<lambda> f::nat\<Rightarrow>'b::ordered_euclidean_space. sum f {0..n}) ` PiE {0..n} B 
           = (\<lambda> f. sum f {0..n}) ` {f. (\<forall>x\<in>{0..n}. f x \<in> B x)}"
  apply (simp add: PiE_Collect image_Collect)
  apply auto
  apply (rule_tac x="\<lambda> x. if x \<in> {0..n} then f x else undefined" in exI)
  apply auto
  done

term sum_list

lemma f2: 
  "(\<lambda> f::nat\<Rightarrow>'b::ordered_euclidean_space. sum f {0..n}) ` PiE {0..n} B 
   = (\<lambda> f. sum_list (map f [0..<n+1])) ` {f. (\<forall>x\<in>{0..n}. f x \<in> B x)}"
  by (simp add: f1, simp add: sum_as_sum_list)

lemma f3: 
  "(\<lambda> f::nat\<Rightarrow>'b::ordered_euclidean_space. sum f {0..n}) ` PiE {0..n} B 
   = sum_list ` {map f [0..<n+1]| f. (\<forall>x\<in>{0..n}. f x \<in> B x)}"
  apply (simp add: f2, auto simp add: image_Collect)
  by force

lemma "(\<lambda> f::nat\<Rightarrow>real. sum f {0..0}) ` PiE {0..0} ((\<lambda>x. undefined)(0::nat := {1::nat}, 1 := {1})) = {1}"
  apply (simp add: PiE_Collect)
  apply (simp add: image_def)
  apply auto
  apply (rule_tac x="\<lambda> x. if x = 0 then 1 else undefined" in exI)
  apply simp
  done

value "map (sum id \<circ> (\<lambda>x. undefined)(0::nat := {1::nat}, 1 := {1})) [0..<1]"

lemma f4: 
  "(\<lambda> f::nat\<Rightarrow>real. sum f {0..n}) ` PiE {0..n} B 
   = set (map (sum id \<circ> B) [0..<n+1])"
  nitpick
  apply (simp add: sum_as_sum_list)
  apply auto
  apply (simp add: f2, auto simp add: image_Collect sum_as_sum_list)


declare [[show_sorts]]

lemma "(\<lambda> f::nat\<Rightarrow>'b::ordered_euclidean_space. sum f A) ` PiE A B = sum id ` (B ` A)"
  apply (simp add: f1)
  apply (auto simp add: image_def)
  apply (rule_tac x="\<lambda> x. if x \<in> A then f x else undefined" in exI)
  apply auto
  done


(* Related to Cartesian product, relate to the pair measure *)
lemma (in prob_space) emeasure_stream_space_scylinder: 
  "measure (stream_space M) (scylinder S (A#X)) = measure M A * measure (stream_space M) (scylinder S X)"
  apply simp
  sorry

lemma stream_snth_Suc: "{x \<in> space (stream_space bool_measure). x !! Suc i} = (\<lambda> (x, xs). x ## xs) ` (UNIV \<times> {x \<in> space (stream_space bool_measure). x !! i})"
  apply auto
  apply (smt (z3) SigmaI UNIV_def mem_Collect_eq pair_imageI space_stream_space stream.sel(2) streams.simps)
  apply (simp add: space_stream_space)
  done

lemma stream_space_snth_scylinder: "{x\<in> space (stream_space bool_measure). x !! i} = scylinder UNIV (replicate i UNIV @ [{True}])"
  apply (induct i)
   apply (simp add: space_stream_space)
  apply (simp only: stream_snth_Suc)
  apply (simp add: set_eq_iff)
  apply safe
   apply auto[1]
  apply simp
  apply (metis UNIV_I mem_Sigma_iff pair_imageI stream.exhaust stream.sel(2))
  done

lemma "ennreal (bool_stream.prob (scylinder UNIV (replicate i UNIV @ [{True}]))) = ennreal 0.5"
proof (induct i)
  case 0
  then show ?case
    apply (simp del: scylinder.simps)
    apply (subst prob_space.emeasure_stream_space_scylinder)
     defer
     apply (simp add: bool_prob_True)
    using bool_space.prob_space apply simp
  next
  case (Suc i)
  then show ?case
    apply (simp del: scylinder.simps)
    apply (subst prob_space.emeasure_stream_space_scylinder)
    defer
    using bool_space.prob_space apply fastforce
    

  qed

lemma "ennreal (bool_stream.prob ({x\<in> space (stream_space bool_measure). x !! i})) = ennreal 0.5"
  apply (subst prob_space.prob_stream_space)
    apply (simp add: Random_Walk.bool_prod.prob_space)
   defer
  apply (unfold bool_measure_def)
  apply (subst nn_integral_scale_measure)
    apply (fold bool_measure_def)
    apply measurable
   apply (subst nn_integral_count_space_finite)
    apply simp
  apply (simp add: UNIV_bool)
  
    apply simp


lemma "bool_stream.prob ({x. x !! i} \<inter> space (stream_space bool_measure)) = 0.5"
  apply (simp add: space_stream_space)
  apply (subst bool_stream.indep_setD)
     apply (simp_all)
   apply (simp add: bool_stream.indep_set_def bool_stream.indep_sets_def)
  apply rule

lemma "bool_stream.expectation (\<lambda>\<omega>. if \<omega> !! i then 1::real else - 1) = 0"
  apply (subst If_indicator)
  apply (subst Bochner_Integration.integral_add)
    apply simp_all
  defer
    defer
  apply auto
    apply (subst Bochner_Integration.integrable_real_indicator)
      
  apply (subst integral_distr[where g="\<lambda> \<omega>. \<omega> !! i" and f="\<lambda> b. if b then 1 else -1" and M="stream_space bool_measure" and N="bool_measure", THEN sym])
  apply simp
  apply (simp add: borel_measurable_const measurable_If)

lemma "bool_stream.expectation (random_walk n) = 0"
  apply (simp add: process_random_walk)
  apply (subst Bochner_Integration.integral_sum)
  defer
proof (induct n)
  case 0
  then show ?case
    unfolding random_walk_def
    apply (subst bool_stream.process_of_apply)
       apply auto
    apply measurable
    by (simp add: measurable_ident_sets sets_stream_space_cong)
next
  case (Suc n)
  have *: "random_walk (Suc n) = (\<lambda>\<omega>. random_walk n \<omega> + (if \<omega> !! (Suc n) then 1 else -1))"
    by (auto simp add: process_random_walk)
  have "bool_stream.expectation (random_walk (Suc n)) = bool_stream.expectation (random_walk n) + bool_stream.expectation (\<lambda>\<omega>. if \<omega> !! (Suc n) then 1 else -1)"
    apply (subst *)
    apply (rule Bochner_Integration.integral_add)
    using integrable_random_walk apply blast
    apply simp
    done
  then show ?case
    find_theorems bool_stream.expectation
    using Suc apply simp
    apply (simp add: bool_measure_def)
    find_theorems scale_measure
    apply (subst prob_space.integral_stream_space)
    apply simp_all
    using bool_space.prob_space_axioms apply fastforce
    using integrable_random_walk_sum
    apply (rule bool_stream.standard_normal_distributed_expectation)
    
    
    sorry
  qed

  thm vimage_algebra_def

end