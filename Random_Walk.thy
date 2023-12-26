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

lemma (in prob_space) integral_stream_space:
  fixes f :: "'a stream \<Rightarrow> 'b::{banach, second_countable_topology}"
  assumes "integrable (stream_space M) f"
  shows "(\<integral>X. f X \<partial>stream_space M) = \<integral>x. (\<integral>X. f (x ## X) \<partial>stream_space M) \<partial>M"
proof -
  interpret S: sequence_space M ..
  interpret P: pair_sigma_finite M "\<Pi>\<^sub>M i::nat\<in>UNIV. M" ..

  have "(\<integral>X. f X \<partial>stream_space M) = (\<integral>X. f (to_stream X) \<partial>S.S)"
    using assms by (subst stream_space_eq_distr) (simp add: integral_distr)
  also have "\<dots> = (\<integral>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X)) \<partial>(M \<Otimes>\<^sub>M S.S))"
    using assms by (subst S.PiM_iter[symmetric]) (simp add: integral_distr)
  also have "\<dots> = (\<integral>x. \<integral>X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) (x, X))) \<partial>S.S \<partial>M)"
    apply (subst P.integral_fst')
    using assms apply auto
    apply (subst P.integrable_product_swap_iff[symmetric])
    apply (simp add: to_stream_nat_case)
    using integrable_distr stream_space_eq_distr  
    sorry (* there's an isomorphism here *)
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

lemma independent_coin_tosses: "bool_stream.indep_vars (\<lambda>_. sigma UNIV UNIV) (\<lambda>n \<omega>. if \<omega> !! n then 1 else (-1:: real)) UNIV"
  apply (simp add: bool_stream.indep_vars_iff_distr_eq_PiM)
  apply (subst stream_space_eq_distr)
  apply (subst distr_distr)
    apply measurable
    apply (simp add: measurable_ident_sets sets_stream_space_cong)
   apply simp
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

lemma source_random_walk[simp]: "proc_source random_walk = stream_space bool_measure"
  and target_random_walk[simp]: "proc_target random_walk = borel"
  and process_random_walk[simp]: "process random_walk = (\<lambda>n \<omega>. \<Sum>j = 1..n. if \<omega> !! j then 1 else -1)"
  unfolding random_walk_def using random_walk_measurable sorry

lemma "bool_stream.expectation (random_walk n) = 0"
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
    by auto
  have "bool_stream.expectation (random_walk (Suc n)) = bool_stream.expectation (random_walk n) + bool_stream.expectation (\<lambda>\<omega>. if \<omega> !! (Suc n) then 1 else -1)"
    apply (subst *)
    apply (rule Bochner_Integration.integral_add)
    unfolding real_integrable_def
     apply auto
         apply (measurable, simp add: measurable_ident_sets sets_stream_space_cong)
    sorry
    then show ?case
      using Suc apply simp sorry
  qed

  thm vimage_algebra_def

end