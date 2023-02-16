theory Kernel
  imports "HOL-Probability.Probability"
begin

section \<open> Kernel type \<close>

text \<open> Let M and M' be measure spaces. A (\<sigma>-) finite transition kernel is a map
   K :: (space M) => (sets M') => ennreal, which satisfies the following conditions:

  \<omega> -> K \<omega> A' is M-measurable (w.r.t. borel - Not in the textbook) for any A' in sets M'
  A' -> K \<omega> A' is a (\<sigma>-) finite measure on M' for any \<omega> in space M \<close>

text \<open> A stochastic transition kernel can be understood as the generalisation of a transition matrix
  for Markov chains. In this analogy, a transition kernel maps the current state \<omega> to a probability
  distribution over possible future state. Indeed, when restricted to a countable state space the
  two definitions coincide. \<close>

locale transition_kernel =
  fixes M :: "'a measure"
    and M' :: "'b measure"
    and \<kappa> :: "'a \<Rightarrow> 'b set \<Rightarrow> ennreal"
  assumes
    sets_target_measurable [measurable]: "\<And>A'. A' \<in> sets M' \<Longrightarrow> (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel" and
    space_source_measure: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> measure_space (space M') (sets M') (\<lambda>A'. \<kappa> \<omega> A')"

lemma transition_kernelI [intro]:
  assumes "\<And>A'. A' \<in> sets M' \<Longrightarrow> (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel"
      and "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> measure_space (space M') (sets M') (\<lambda>A'. \<kappa> \<omega> A')"
    shows "transition_kernel M M' \<kappa>"
  using assms by (fact Kernel.transition_kernel.intro)

lemma transition_kernel_restrict [simp]:
  assumes "transition_kernel M M' \<kappa>"
  shows "transition_kernel M M' (\<lambda> \<omega> A'. if \<omega> \<in> space M \<and> A' \<in> sets M' then \<kappa> \<omega> A' else 0)"
  apply (unfold_locales)
    using assms transition_kernel.sets_target_measurable apply fastforce
    apply (smt (verit, del_insts) assms transition_kernel.space_source_measure measure_space_eq sets.sigma_sets_eq sets.space_closed)
    done

lemma transition_kernel_zero [simp]: "transition_kernel M M' (\<lambda>\<omega> A'. 0)"
  apply unfold_locales
   apply auto
   apply (metis measure_space_0 sets.sigma_sets_eq sets.space_closed)
  done

lemma (in transition_kernel) measure_space_restrict_kernel:
  "measure_space (space M') (sets M') (\<lambda>A'. if \<omega> \<in> space M \<and> A' \<in> sets M' then \<kappa> \<omega> A' else 0)"
  apply (cases "\<omega> \<in> space M")
    apply (smt (verit, ccfv_SIG) measure_space_eq sets.sigma_sets_eq sets.space_closed space_source_measure)
    apply (auto, metis measure_space_0 sets.sigma_sets_eq sets.space_closed)
  done

lemma (in transition_kernel)
  assumes "\<omega> \<in> space M"
  shows positive: "positive (sets M') (\<kappa> \<omega>)"
  and countably_additive: "countably_additive (sets M') (\<kappa> \<omega>)"
  using space_source_measure[OF assms] unfolding measure_space_def by (simp_all)

text \<open> Klenke remark 8.26 \<close>
lemma kernel_measurable_pi_system:
  assumes "\<And>A'. A' \<in> P \<Longrightarrow> (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel" "Int_stable P" "sigma_sets (space M') P = sets M'" "space M' \<in> P"
  shows "\<And>A'. A' \<in> sets M' \<Longrightarrow> (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel"
proof -
  have D: "Dynkin_system (space M') {A' \<in> sets M'. (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel}"
  proof (intro Dynkin_systemI)
    oops (* Doesn't seem obvious at all *)

text \<open> The boilerplate definitions for the kernel type follow closely those of the measure type
   @{typ "'a measure"}\<close>

typedef ('a, 'b) kernel =
  "{(M :: 'a measure, M' :: 'b measure, \<kappa>). 
    transition_kernel M M' \<kappa> \<and> (\<forall>\<omega>. \<forall>A'. \<omega> \<in> -space M \<or> A' \<in> -sets M' \<longrightarrow> \<kappa> \<omega> A' = 0)}"
  using transition_kernel_zero by blast

definition kernel_source :: "('a, 'b) kernel \<Rightarrow> 'a measure" where
"kernel_source K = fst (Rep_kernel K)"

definition kernel_target :: "('a, 'b) kernel \<Rightarrow> 'b measure" where
"kernel_target K = fst (snd (Rep_kernel K))"

definition kernel :: "('a, 'b) kernel \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> ennreal" where
"kernel K = snd (snd (Rep_kernel K))"

declare [[coercion kernel_source]]
declare [[coercion kernel_target]]
declare [[coercion kernel]]

interpretation kernel: transition_kernel "kernel_source K" "kernel_target K" "kernel K"
  by (cases K) (auto simp: kernel_source_def kernel_target_def kernel_def Abs_kernel_inverse)

lemma kernel_not_sets_zero[simp]: "A' \<notin> sets (kernel_target K) \<Longrightarrow> kernel K \<omega> A' = 0"
  by (cases K) (auto simp add: kernel_def Abs_kernel_inverse kernel_target_def)

lemma kernel_not_space_zero[simp]: "\<omega> \<notin> space (kernel_source K) \<Longrightarrow> kernel K \<omega> A' = 0"
  by (cases K) (auto simp add: kernel_def Abs_kernel_inverse kernel_source_def)

lemma kernel_empty [simp]: "kernel K \<omega> {} = 0"
  apply (cases "\<omega> \<in> space (kernel_source K)")
    apply (metis kernel.space_source_measure emeasure_empty emeasure_measure_of_conv sets.empty_sets sets.sigma_sets_eq)
    apply (fact kernel_not_space_zero)
  done

definition kernel_of :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b set \<Rightarrow> ennreal) \<Rightarrow> ('a, 'b) kernel"
  where
"kernel_of M M' \<kappa> =
   Abs_kernel (M, M',
   \<lambda>\<omega> A'. if \<omega> \<in> space M \<and> A' \<in> sets M' \<and> transition_kernel M M' \<kappa> then \<kappa> \<omega> A' else 0)"

lemma transition_kernel_kernel_of [simp]: "transition_kernel M M' 
  (\<lambda>\<omega> A'. if \<omega> \<in> space M \<and> A' \<in> sets M' \<and> transition_kernel M M' \<kappa> then \<kappa> \<omega> A' else 0)"
  by (cases "transition_kernel M M' \<kappa>") auto
                                                                
lemma source_kernel_of [simp]: "kernel_source (kernel_of M M' \<kappa>) = M"
  unfolding kernel_of_def kernel_source_def apply (subst Abs_kernel_inverse)
  by auto

lemma target_kernel_of [simp]: "kernel_target (kernel_of M M' \<kappa>) = M'"
  unfolding kernel_of_def kernel_target_def apply (subst Abs_kernel_inverse)
  by auto

lemma kernel_apply_kernel_of [simp]:
  assumes "\<omega> \<in> space M" "A' \<in> sets M'" "transition_kernel M M' \<kappa>"
  shows "kernel (kernel_of M M' \<kappa>) \<omega> A' = \<kappa> \<omega> A'"
  unfolding kernel_of_def apply (simp add: kernel_def)
  apply (subst Abs_kernel_inverse)
  using assms apply auto
  done

text \<open> Homogeneous kernel \<close>
typedef 'a hkernel = "{K :: ('a, 'a) kernel. kernel_source K = kernel_target K}"
  morphisms from_hkernel hkernel
  by (simp, metis source_kernel_of target_kernel_of)

declare [[coercion from_hkernel]]

definition hkernel_space :: "'a hkernel \<Rightarrow> 'a measure" where
[simp]: "hkernel_space K \<equiv> kernel_source (from_hkernel K)"

lemma hkernel_source_eq_target: 
  "kernel_source (from_hkernel K) = kernel_target (from_hkernel K)"
  using from_hkernel by auto

lemma from_hkernel_kernel_of_inverse [simp]:
  "from_hkernel (hkernel (kernel_of M M \<kappa>)) = (kernel_of M M \<kappa>)"
  by (simp add: hkernel_inverse)

definition kernel_measure :: "('a, 'b) kernel \<Rightarrow> 'a \<Rightarrow> 'b measure" where
"kernel_measure K \<omega> = measure_of (space (kernel_target K)) (sets (kernel_target K)) (kernel K \<omega>)"

lemma kernel_measure_space [simp]: "space (kernel_measure K \<omega>) = space (kernel_target K)"
  by (simp add: kernel_measure_def)

lemma kernel_measure_sets [simp]: "sets (kernel_measure K \<omega>) = sets (kernel_target K)"
  by (simp add: kernel_measure_def)

lemma kernel_measure_emeasure: "emeasure (kernel_measure K \<omega>) = kernel K \<omega>"
  unfolding kernel_measure_def
  apply (subst emeasure_measure_of_conv)
  apply (auto simp add: fun_eq_iff)
   apply (metis kernel_not_sets_zero sets.sigma_sets_eq)
  by (metis kernel_not_space_zero sets.sigma_sets_eq kernel.space_source_measure)

lemma measurable_kernel_measure: "(f \<in> (kernel_measure K \<omega>) \<rightarrow>\<^sub>M M) = (f \<in> (kernel_target K) \<rightarrow>\<^sub>M M)"
  by (metis kernel_measure_sets measurable_cong_sets)

locale sigma_finite_kernel =
  fixes K :: "('a, 'b) kernel"
  assumes sigma_finite_measures:
    "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> sigma_finite_measure (kernel_measure K \<omega>)"

locale finite_kernel = sigma_finite_kernel +
  assumes finite_measures:  "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> finite_measure (kernel_measure K \<omega>)"

lemma finite_kernelI:
  assumes "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> finite_measure (kernel_measure K \<omega>)"
  shows "finite_kernel K"
  apply (unfold_locales)
   apply (meson assms finite_measure.sigma_finite_measure sigma_finite_measure_def)
   using assms finite_measure.emeasure_finite apply blast
   done

lemma finite_kernel_finite:
  assumes "finite_kernel K"
  shows "K \<omega> A \<noteq> \<infinity>"
proof (cases "\<omega> \<in> space (kernel_source K)")
  case False
  then show ?thesis by simp
next
  case True
  then have "finite_measure (kernel_measure K \<omega>)"
    by (simp add: finite_kernel.finite_measures assms)
  then have "emeasure (kernel_measure K \<omega>) A \<noteq> \<infinity>"
    using finite_measure.emeasure_finite by auto
  then show "K \<omega> A \<noteq> \<infinity>"
    by (metis kernel_measure_emeasure)
qed

locale stochastic_kernel = finite_kernel +
  assumes probability_measures: "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> prob_space (kernel_measure K \<omega>)"

lemma stochastic_kernelI:
  assumes "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> prob_space (kernel_measure K \<omega>)"
  shows "stochastic_kernel K"
  using assms apply (unfold_locales)
    apply (meson prob_space_imp_sigma_finite sigma_finite_measure.sigma_finite_countable)
  using prob_space.measure_le_1 prob_space.not_empty subprob_space.emeasure_subprob_space_less_top subprob_spaceI apply blast
  using prob_space.emeasure_space_1 apply blast
  done

lemma (in stochastic_kernel) kernel_space_eq_1 [simp]:
  assumes "\<omega> \<in> space (kernel_source K)"
  shows "K \<omega> (space K) = 1"
  by (metis probability_measures[OF assms] kernel_measure_emeasure 
            kernel_measure_space prob_space.emeasure_space_1)

locale substochastic_kernel = finite_kernel +
  assumes subprob_measures: "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> subprob_space (kernel_measure K \<omega>)"

sublocale stochastic_kernel \<subseteq> substochastic_kernel
  by (simp add: finite_kernel_axioms prob_space_imp_subprob_space probability_measures
      substochastic_kernel_axioms.intro substochastic_kernel_def)

lemma substochastic_kernelI:
  assumes "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> subprob_space (kernel_measure K \<omega>)"
  shows "substochastic_kernel K"
  using assms apply (unfold_locales)
  using subprob_space_imp_sigma_finite sigma_finite_measure.sigma_finite_countable
        subprob_space.emeasure_subprob_space_less_top subprob_space.emeasure_space_le_1
        subprob_space.subprob_not_empty by meson+

lemma (in substochastic_kernel) kernel_leq_1 [simp]: "kernel K \<omega> A' \<le> 1"
  apply (cases "\<omega> \<in> space (kernel_source K) \<and> A' \<in> sets (kernel_target K)")
   apply (metis subprob_measures kernel_measure_emeasure subprob_space.subprob_emeasure_le_1)
   apply auto
  done

lemma kernel_of_eq:
  assumes "\<And>\<omega> A'. \<omega> \<in> space M \<and> A' \<in> sets M' \<Longrightarrow> \<kappa> \<omega> A' = \<kappa>' \<omega> A'"
  shows "kernel_of M M' \<kappa> = kernel_of M M' \<kappa>'"
  unfolding kernel_of_def apply (subst Abs_kernel_inject)
  using assms apply (auto simp add: fun_eq_iff)
  unfolding transition_kernel_def
  by (smt (verit, ccfv_SIG) measurable_cong measure_space_eq sets.sigma_sets_eq sets.space_closed)+

text \<open> Klenke lemma 14.23 \<close>

lemma kernel_measure_pair_integral_measurable [measurable]:
  fixes f :: "'a \<times> 'b \<Rightarrow> ennreal"
    and K :: "('a, 'b) kernel"
  assumes f_measurable[measurable]: "f \<in> borel_measurable (kernel_source K \<Otimes>\<^sub>M kernel_target K)"
      and finite_K: "finite_kernel K"              
  defines "I \<equiv> \<lambda> f. (\<lambda>\<omega>\<^sub>1. \<integral>\<^sup>+\<omega>\<^sub>2. f(\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1)"
  shows "I f \<in> borel_measurable (kernel_source K)"
proof -
  let ?\<Omega>\<^sub>1 = "space (kernel_source K)" and ?\<Omega>\<^sub>2 = "space (kernel_target K)"
  and ?A\<^sub>1 = "sets (kernel_source K)"  and ?A\<^sub>2 = "sets (kernel_target K)"
  have f_snd_measurable[measurable]: "(\<lambda>\<omega>\<^sub>2. f (\<omega>\<^sub>1, \<omega>\<^sub>2)) \<in> borel_measurable (kernel_target K)"
    if "\<omega>\<^sub>1 \<in> space (kernel_source K)" for \<omega>\<^sub>1
    using that by measurable
  {
    fix A\<^sub>1 A\<^sub>2
    assume *: "A\<^sub>1 \<in> ?A\<^sub>1" "A\<^sub>2 \<in> ?A\<^sub>2"
    then have "I (indicator (A\<^sub>1 \<times> A\<^sub>2)) = (\<lambda>\<omega>\<^sub>1. indicator A\<^sub>1 \<omega>\<^sub>1 * kernel K \<omega>\<^sub>1 A\<^sub>2)"
      unfolding I_def apply (subst nn_integral_eq_simple_integral)
      unfolding kernel_measure_def apply (auto simp: indicator_times)
      by (metis kernel_measure_def kernel_measure_emeasure)
    also have "... \<in> borel_measurable (kernel_source K)"
      using * by measurable
    finally have "I (indicator (A\<^sub>1 \<times> A\<^sub>2)) \<in> borel_measurable (kernel_source K)" .
  } note I_indicator_prod_measurable [measurable] = this
  define D where "D \<equiv> {A \<in> sets (kernel_source K \<Otimes>\<^sub>M kernel_target K). I (indicator A) \<in> borel_measurable (kernel_source K)}"
  have Dynkin_D: "Dynkin_system (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) D"
  proof
    show D_subset: "D \<subseteq> Pow (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)"
      using sets.sets_into_space space_pair_measure D_def by fastforce
    show "(?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) \<in> D"
      unfolding D_def by measurable
    {
      fix A assume A: "A \<in> D"
      then have "I (indicator A) \<in> borel_measurable (kernel_source K)"
                "I (indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)) \<in> borel_measurable (kernel_source K)"
        unfolding D_def by simp_all
      then have "(\<lambda>\<omega>\<^sub>1. I (indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)) \<omega>\<^sub>1 - I (indicator A) \<omega>\<^sub>1) \<in> borel_measurable (kernel_source K)"
        by measurable
      moreover have "\<And>\<omega>\<^sub>1. \<omega>\<^sub>1 \<in> ?\<Omega>\<^sub>1 \<Longrightarrow> I (indicator ((?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) - A)) \<omega>\<^sub>1 =
         I (indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)) \<omega>\<^sub>1 - I (indicator A) \<omega>\<^sub>1"
      proof -
        fix \<omega>\<^sub>1 assume \<omega>\<^sub>1: "\<omega>\<^sub>1 \<in> ?\<Omega>\<^sub>1"
        then have finite_integral: "(\<integral>\<^sup>+ x. indicator A (\<omega>\<^sub>1, x) \<partial>kernel_measure K \<omega>\<^sub>1) < \<infinity>"
        proof -
          have "integral\<^sup>N (kernel_measure K \<omega>\<^sub>1) (\<lambda>x. indicator A (\<omega>\<^sub>1, x)) \<le> integral\<^sup>N (kernel_measure K \<omega>\<^sub>1) (indicator ?\<Omega>\<^sub>2)"
            apply (rule nn_integral_mono)
            by (simp add: indicator_def)
          also have "... < \<infinity>"
            apply auto
            by (meson \<omega>\<^sub>1 finite_K finite_kernel.finite_measures finite_measure.emeasure_finite top.not_eq_extremum)
          finally show ?thesis .
        qed
        have "I (indicator ((?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) - A)) \<omega>\<^sub>1 = \<integral>\<^sup>+\<omega>\<^sub>2. (indicator ((?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) - A))(\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1"
          unfolding I_def ..
        also have "... =  \<integral>\<^sup>+\<omega>\<^sub>2. indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)(\<omega>\<^sub>1, \<omega>\<^sub>2) - indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1"
          by (smt (verit, del_insts) Diff_iff ennreal_0 ennreal_1 ennreal_minus_if indicator_simps nn_integral_cong)
        also have "... = (\<integral>\<^sup>+\<omega>\<^sub>2. indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)(\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1) 
                          - (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1)"
          apply (rule nn_integral_diff)
          using \<omega>\<^sub>1 apply measurable
             apply (simp add: measurable_ident_sets)
          using \<omega>\<^sub>1 A apply (measurable, auto)
           unfolding pred_def apply (auto simp add: D_def)[1]
           using finite_integral by auto
        finally show "I (indicator ((?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) - A)) \<omega>\<^sub>1 = I (indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)) \<omega>\<^sub>1 - I (indicator A) \<omega>\<^sub>1"
          unfolding I_def .
      qed
      ultimately have "I (indicator ((?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) - A)) \<in> borel_measurable (kernel_source K)"
        by (subst measurable_cong, auto)
    }
    then show "\<And>A. A \<in> D \<Longrightarrow> ?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2 - A \<in> D"
      unfolding D_def by blast
    show "\<And>A :: nat \<Rightarrow> ('a \<times> 'b) set. disjoint_family A \<Longrightarrow> range A \<subseteq> D \<Longrightarrow> \<Union> (range A) \<in> D"
    proof (auto simp: D_def)
      fix A :: "nat \<Rightarrow> ('a \<times> 'b) set" assume *: "disjoint_family A" 
        "range A \<subseteq> {A \<in> sets (kernel_source K \<Otimes>\<^sub>M kernel_target K). I (indicator A) \<in> borel_measurable (kernel_source K)}"
      then have "A i \<in> sets (kernel_source K \<Otimes>\<^sub>M kernel_target K)" for i
        by blast
      then have [measurable]: "indicator (A i) \<in> borel_measurable (kernel_source K \<Otimes>\<^sub>M kernel_target K)" for i
        using borel_measurable_indicator by blast
      have "\<And>\<omega>\<^sub>1. \<omega>\<^sub>1 \<in> ?\<Omega>\<^sub>1 \<Longrightarrow> I (indicator (\<Union> (range A))) \<omega>\<^sub>1 = (\<Sum>n. I (indicator (A n)) \<omega>\<^sub>1)"
        unfolding I_def
        apply (subst suminf_indicator[THEN sym])
        using * apply auto
        apply (rule nn_integral_suminf)
        apply (subst measurable_kernel_measure)
        by measurable
      moreover have "(\<lambda>\<omega>\<^sub>1. \<Sum>n. I (indicator (A n)) \<omega>\<^sub>1) \<in> borel_measurable (kernel_source K)"
        apply measurable
        using *(2) by blast
      ultimately show "I (indicator (\<Union> (range A))) \<in> borel_measurable (kernel_source K)"
        using measurable_cong by force
    qed
  qed

  moreover have "{a \<times> b | a b. a \<in> sets (kernel_source K) \<and> b \<in> sets (kernel_target K)} \<subseteq> D"
    using D_def by auto
  moreover have "Int_stable {a \<times> b | a b. a \<in> sets (kernel_source K) \<and> b \<in> sets (kernel_target K)}"
    using Int_stable_pair_measure_generator by blast
  ultimately have "sigma_sets (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) {a \<times> b | a b. a \<in> sets (kernel_source K) \<and> b \<in> sets (kernel_target K)} = Dynkin (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) D"
    apply (subst sigma_eq_Dynkin)
      apply (metis pair_measure_closed)
     apply blast
    apply auto
     apply (metis (no_types, lifting) Dynkin_system.Dynkin_idem Dynkin_system.Dynkin_subset in_mono)
    by (smt (verit) Collect_cong D_def Dynkin_system.Dynkin_idem Sigma_cong mem_Collect_eq pair_measure_closed sets_pair_measure sigma_eq_Dynkin)
  then have "sets (kernel_source K \<Otimes>\<^sub>M kernel_target K) = D"
    by (smt (verit) Collect_cong Dynkin_system.Dynkin_idem Sigma_cong Dynkin_D sets_pair_measure)
  then have [measurable]: "\<And>A. A \<in> sets (kernel_source K \<Otimes>\<^sub>M kernel_target K) \<Longrightarrow> I (indicator A) \<in> borel_measurable (kernel_source K)"
    unfolding D_def by blast
  then have simple_I_measurable [measurable]:
    "\<And>g. simple_function (kernel_source K \<Otimes>\<^sub>M kernel_target K) g \<Longrightarrow> I g \<in> borel_measurable (kernel_source K)"
  proof -
    fix g :: "'a \<times> 'b \<Rightarrow> ennreal"
    let ?M = "(kernel_source K \<Otimes>\<^sub>M kernel_target K)"
    assume *: "simple_function ?M g"
    then have [measurable]:"g \<in> borel_measurable ?M"
      by (simp add: borel_measurable_simple_function)
    have g: "g x = (\<Sum>y \<in> g ` space ?M. y * indicator (g -` {y} \<inter> space ?M) x)" if "x \<in> space ?M" for x
      using simple_function_indicator_representation[OF * that] by blast
    {
      fix \<omega>\<^sub>1 assume *: "\<omega>\<^sub>1 \<in> ?\<Omega>\<^sub>1"
      have "I g \<omega>\<^sub>1 = (\<integral>\<^sup>+\<omega>\<^sub>2. g(\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1)"
        unfolding I_def ..
      also have "...  = (\<integral>\<^sup>+\<omega>\<^sub>2. (\<Sum>y \<in> g ` space ?M. y * (indicator (g -` {y} \<inter> space ?M)(\<omega>\<^sub>1, \<omega>\<^sub>2))) \<partial>kernel_measure K \<omega>\<^sub>1)"
        by (smt (verit, ccfv_SIG) kernel_measure_space mem_Sigma_iff nn_integral_cong space_pair_measure sum.cong * g)
      also have "... = (\<Sum>y \<in> g ` space ?M. (\<integral>\<^sup>+\<omega>\<^sub>2. y * (indicator (g -` {y} \<inter> space ?M)(\<omega>\<^sub>1, \<omega>\<^sub>2)) \<partial>kernel_measure K \<omega>\<^sub>1))"
        apply (rule nn_integral_sum)
        using * apply measurable
        apply (simp add: measurable_ident_sets)
        apply (smt (verit, ccfv_threshold) "*" kernel_measure_space measurable_cong mem_Sigma_iff pred_intros_logic(1) space_pair_measure)
        done
      also have "... = (\<Sum>y \<in> g ` space ?M. y * (\<integral>\<^sup>+\<omega>\<^sub>2. (indicator (g -` {y} \<inter> space ?M)(\<omega>\<^sub>1, \<omega>\<^sub>2)) \<partial>kernel_measure K \<omega>\<^sub>1))"
        apply (subst nn_integral_cmult)
        apply auto
        apply (subst measurable_kernel_measure)
         apply measurable
        using * by auto
      also have "... = (\<Sum>y \<in> g ` space ?M. y * I (indicator (g -` {y} \<inter> space ?M)) \<omega>\<^sub>1)"
        unfolding I_def ..
      finally have "I g \<omega>\<^sub>1 = (\<Sum>y \<in> g ` space ?M. y * I (indicator (g -` {y} \<inter> space ?M)) \<omega>\<^sub>1)"
        .
    } note indicator_repr = this
    have "(\<lambda>\<omega>\<^sub>1. (\<Sum>y \<in> g ` space ?M. y * I (indicator (g -` {y} \<inter> space ?M)) \<omega>\<^sub>1)) \<in> borel_measurable (kernel_source K)"
      using * by measurable
    then show "I g \<in> borel_measurable (kernel_source K)"
      by (metis (no_types, lifting) measurable_cong indicator_repr)
  qed
  obtain f' where f': "incseq f' \<and> (\<forall>i. (\<forall>x. f' i x < top) \<and> simple_function (kernel_source K \<Otimes>\<^sub>M kernel_target K) (f' i)) \<and> f = (SUP i. f' i)"
    using borel_measurable_implies_simple_function_sequence[OF f_measurable] by blast
  then have "\<And>\<omega>\<^sub>1. \<omega>\<^sub>1 \<in> ?\<Omega>\<^sub>1 \<Longrightarrow> I f \<omega>\<^sub>1 = (SUP i. I (f' i) \<omega>\<^sub>1)"
    unfolding I_def
    apply (subst nn_integral_monotone_convergence_SUP[THEN sym])
    using mono_compose apply blast
    apply (smt (verit, best) borel_measurable_simple_function kernel_measure_sets measurable_Pair2 measurable_cong measurable_cong_sets)
    apply (metis SUP_apply)
    done
  moreover have "(\<lambda>\<omega>\<^sub>1. (SUP i. I (f' i) \<omega>\<^sub>1)) \<in> borel_measurable (kernel_source K)"
    by (measurable, simp add: f')
  ultimately show ?thesis
    using measurable_cong by force
qed

corollary kernel_measure_integral_measurable[measurable]:
  fixes f :: "'b \<Rightarrow> ennreal"
    and K :: "('a, 'b) kernel"
  assumes f_measurable[measurable]: "f \<in> borel_measurable (kernel_target K)"
      and finite_K: "finite_kernel K"              
  defines "I \<equiv> \<lambda> f. (\<lambda>\<omega>\<^sub>1. \<integral>\<^sup>+\<omega>\<^sub>2. f \<omega>\<^sub>2 \<partial>kernel_measure K \<omega>\<^sub>1)"
  shows "I f \<in> borel_measurable (kernel_source K)"
proof -
  let ?f' = "\<lambda>(x,y). f y"
  have "?f' \<in> borel_measurable (kernel_source K \<Otimes>\<^sub>M kernel_target K)"
    by measurable
  then have "(\<lambda>\<omega>\<^sub>1. \<integral>\<^sup>+\<omega>\<^sub>2. ?f' (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1) \<in> borel_measurable (kernel_source K)"
    using finite_K by measurable
  then show ?thesis
    unfolding I_def by fastforce
qed

section \<open> Kernel examples \<close>

text \<open> Adapted from Bauer, p. 305-307 \<close>

theorem indicator_kernel: "transition_kernel M M (\<lambda>\<omega> A. indicator A \<omega>)"
proof unfold_locales
  fix A' assume "A' \<in> sets M"
  then show "indicator A' \<in> borel_measurable M"
    by measurable
next
  fix \<omega> assume "\<omega> \<in> space M"
  then show "measure_space (space M) (sets M) (\<lambda>A'. indicator A' \<omega>)"
    unfolding measure_space_def apply auto
    apply (simp add: sets.sigma_algebra_axioms)
     apply (simp add: Sigma_Algebra.positive_def)
    unfolding countably_additive_def
    by (auto simp: suminf_indicator)
qed

(* Dirac delta *)
theorem return_kernel[simp]: "transition_kernel M M (return M)"
  apply (rule transition_kernelI)
  by (force, metis measure_space sets_return space_return)

lemma emeasure_transition_kernel: "transition_kernel M M' (\<lambda>\<omega> A. emeasure M' A)"
  apply unfold_locales
   apply measurable
   apply (simp add: measure_space)
  done

lemma
  fixes \<pi> :: "nat \<Rightarrow> nat \<Rightarrow> ennreal"
  shows "transition_kernel (count_space UNIV) (count_space UNIV) (\<lambda>i A. \<Sum>j \<in> A. \<pi> i j)"
  apply (unfold_locales)
  using borel_measurable_count_space apply blast
  unfolding measure_space_def apply auto
    apply (metis Pow_UNIV sigma_algebra_Pow)
   apply (simp add: Sigma_Algebra.positive_def)
  apply (auto simp add: countably_additive_def)
  sorry (* prove that sums on naturals are countably additive *)


definition nat_set_to_seq :: "nat set \<Rightarrow> (nat \<Rightarrow> nat)" where
"nat_set_to_seq N = (\<lambda>n. indicator N n * n)"

(*
lemma
  assumes "disjoint_family (A :: nat \<Rightarrow> nat set)"
  shows "suminf (\<lambda>i. (nat_set_to_seq (A i))) = suminf (nat_set_to_seq (\<Union>i. A i))"*)


end