theory Kernel_Composition
  imports Kernel_Product
begin

text \<open>
  Following Klenke: the composition of kernels k_1 : (\<Omega>_0, A_0) -> (\<Omega>_1, A_1) and
   k_2: (\<Omega>_1, A_1) -> (\<Omega>_2, A_2) is defined by following:
  (\<omega>_0, A_2) \<mapsto> \<integral>_{\<Omega>_1} \<kappa>_1(\<omega>_0, d\<omega>_1) \<kappa>_2(\<omega>_1, A_2) \<close>

definition kernel_comp :: "('a, 'b) kernel \<Rightarrow> ('b, 'c) kernel \<Rightarrow> ('a, 'c) kernel" (infixr "(\<circ>\<^sub>K)" 80) where
"kernel_comp K\<^sub>1 K\<^sub>2 = kernel_of (kernel_source K\<^sub>1) (kernel_target K\<^sub>2)
   (\<lambda>\<omega>\<^sub>0 A\<^sub>2. \<integral>\<^sup>+\<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 A\<^sub>2 \<partial>((kernel_measure K\<^sub>1 \<omega>\<^sub>0)))"

lemma
  source_kernel_comp [simp]: "kernel_source (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) = kernel_source K\<^sub>1" and
  target_kernel_comp [simp]: "kernel_target (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) = kernel_target K\<^sub>2"
  unfolding kernel_comp_def by simp_all

lemma kernel_comp_wf:
  assumes "sets (kernel_source K\<^sub>2) = sets (kernel_target K\<^sub>1)" "finite_kernel K\<^sub>1"
  shows "transition_kernel (kernel_source K\<^sub>1) (kernel_target K\<^sub>2) (\<lambda>\<omega>\<^sub>0 A\<^sub>2. \<integral>\<^sup>+\<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 A\<^sub>2 \<partial>((kernel_measure K\<^sub>1 \<omega>\<^sub>0)))"
proof
  fix A' assume *: "A' \<in> sets (kernel_target K\<^sub>2)"
  show "(\<lambda>\<omega>\<^sub>0. \<integral>\<^sup>+ \<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 A' \<partial>kernel_measure K\<^sub>1 \<omega>\<^sub>0) \<in> borel_measurable (kernel_source K\<^sub>1)"
    apply (rule kernel_measure_integral_measurable[where K = "K\<^sub>1" and f="\<lambda>\<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 A'"])
    using * assms(1) apply measurable
    using assms(2) by blast
next
  fix \<omega> assume "\<omega> \<in> space (kernel_source K\<^sub>1)"
  then show "measure_space (space (kernel_target K\<^sub>2)) (sets (kernel_target K\<^sub>2)) (\<lambda>A'. \<integral>\<^sup>+ \<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 A' \<partial>kernel_measure K\<^sub>1 \<omega>)"
    apply (auto simp: measure_space_def)
      apply (simp add: sets.sigma_algebra_axioms)
     apply (simp add: Sigma_Algebra.positive_def)
    unfolding countably_additive_def apply auto
    apply (subst nn_integral_suminf[THEN sym])
     apply (metis (full_types) UNIV_I assms(1) kernel.sets_target_measurable kernel_measure_sets measurable_cong_sets sets_range)
    apply (rule nn_integral_cong)
    apply (metis kernel_measure_emeasure kernel_measure_sets suminf_emeasure)
    done
qed

corollary kernel_comp_kernel:
  assumes "sets (kernel_source K\<^sub>2) = sets (kernel_target K\<^sub>1)" "finite_kernel K\<^sub>1"
  shows "kernel (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) = (\<lambda>\<omega>\<^sub>0 A\<^sub>2. \<integral>\<^sup>+\<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 A\<^sub>2 \<partial>((kernel_measure K\<^sub>1 \<omega>\<^sub>0)))"
  apply (auto simp add: fun_eq_iff)
  subgoal for \<omega> A'
    apply (cases "\<omega> \<in> space (kernel_source K\<^sub>1) \<and> A' \<in> sets (kernel_target K\<^sub>2)")
    unfolding kernel_comp_def using kernel_comp_wf[OF assms] apply simp
    apply auto
    apply (metis emeasure_null_measure kernel_measure_emeasure kernel_not_space_zero measure_eqI nn_integral_null_measure sets_null_measure)
    done
  done


lemma kernel_comp_substochastic:
  assumes "sets (kernel_source K\<^sub>2) = sets (kernel_target K\<^sub>1)" "substochastic_kernel K\<^sub>1" "substochastic_kernel K\<^sub>2"
  shows "substochastic_kernel (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2)"
proof (rule substochastic_kernelI)
  fix \<omega> assume \<omega>: "\<omega> \<in> space (kernel_source (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2))"
  then have "emeasure (kernel_measure (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) \<omega>) (space (kernel_target K\<^sub>2)) = 
                \<integral>\<^sup>+ \<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 (space (kernel_target K\<^sub>2)) \<partial>kernel_measure K\<^sub>1 \<omega>"
    by (simp add: assms(1,2) kernel_comp_kernel kernel_measure_emeasure substochastic_kernel.axioms(1))
  also have "(\<integral>\<^sup>+ \<omega>\<^sub>1. kernel K\<^sub>2 \<omega>\<^sub>1 (space (kernel_target K\<^sub>2)) \<partial>kernel_measure K\<^sub>1 \<omega>) \<le> (\<integral>\<^sup>+ \<omega>\<^sub>1. 1 \<partial>kernel_measure K\<^sub>1 \<omega>)"
    apply (rule nn_integral_mono)
    by (simp add: assms(3) substochastic_kernel.kernel_leq_1)
  also have "... \<le> 1"
    by (simp add: assms(2) kernel_measure_emeasure substochastic_kernel.kernel_leq_1)
  finally show "subprob_space (kernel_measure (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) \<omega>)"
    by (metis Orderings.order_eq_iff \<omega> assms empty_iff kernel_measure_space sets_eq_imp_space_eq 
        source_kernel_comp subprob_space.subprob_not_empty subprob_spaceI subset_eq substochastic_kernel.subprob_measures target_kernel_comp)
qed

lemma kernel_comp_stochastic:
  assumes "sets (kernel_source K\<^sub>2) = sets (kernel_target K\<^sub>1)" "stochastic_kernel K\<^sub>1" "stochastic_kernel K\<^sub>2"
  shows "stochastic_kernel (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2)"
proof (rule stochastic_kernelI)
  fix \<omega> assume \<omega>: "\<omega> \<in> space (kernel_source (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2))"
  then have "emeasure (kernel_measure (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) \<omega>) (space (kernel_target K\<^sub>2)) = \<integral>\<^sup>+ \<omega>\<^sub>1. 1 \<partial>kernel_measure K\<^sub>1 \<omega>"
    apply (simp only: assms(1,2) kernel_comp_kernel kernel_measure_emeasure stochastic_kernel.axioms(1))
    apply (rule nn_integral_cong)
    by (metis assms(1,3) kernel_measure_space sets_eq_imp_space_eq stochastic_kernel.kernel_space_eq_1)
  also have "... = 1"
    using \<omega> by (auto simp: kernel_measure_emeasure assms(2) stochastic_kernel.kernel_space_eq_1)
  finally show "prob_space (kernel_measure (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) \<omega>)"
    using prob_spaceI by force
qed

text \<open> Theorem 14.29 \<close>

theorem kernel_comp_prod:
  fixes K\<^sub>1 :: "('a, 'b) kernel" and K\<^sub>2 :: "('b, 'c) kernel"
  assumes substochastic: "substochastic_kernel K\<^sub>1" "substochastic_kernel K\<^sub>2"
  and "A\<^sub>2 \<in> sets (kernel_target K\<^sub>2)" "sets (kernel_source K\<^sub>2) = sets (kernel_target K\<^sub>1)"
  shows "kernel (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) \<omega>\<^sub>0 A\<^sub>2 = kernel (K\<^sub>1 \<Otimes>\<^sub>P K\<^sub>2) \<omega>\<^sub>0 (snd -` A\<^sub>2)"
  unfolding kernel_product_partial_def
  apply (cases "\<omega>\<^sub>0 \<in> space (kernel_source K\<^sub>1)")
   defer apply (simp add: kernel_product_partial_def)
  sorry

find_theorems measurable emeasure

text \<open> Lemma 14.30 \<close>
lemma kernel_comp_convolution:
  assumes "prob_space M" "prob_space N" "\<omega> \<in> space M" 
  assumes [measurable_cong]: "sets N = sets borel" "sets M = sets N"
  defines "K\<^sub>1 \<equiv> kernel_of M M (\<lambda>x dy. M dy)"
  and "K\<^sub>2 \<equiv> kernel_of M M (\<lambda>y dz. ((return M y) \<star> N) dz)" 
shows "kernel (K\<^sub>1 \<circ>\<^sub>K K\<^sub>2) \<omega> = emeasure (M \<star> N)"
proof -
  have K1: "kernel K\<^sub>1 x A' = M A'" if "x \<in> space M \<and> A' \<in> sets M" for A' x
    unfolding K\<^sub>1_def
    by (metis that emeasure_transition_kernel kernel_apply_kernel_of)
  have K1_measure: "kernel_measure K\<^sub>1 \<omega> = M"
    unfolding kernel_measure_def K\<^sub>1_def apply auto
    by (metis K1 K\<^sub>1_def assms(3) kernel_measure_def kernel_measure_emeasure measure_eqI sets.sets_measure_of_eq target_kernel_of)
  have K2: "kernel K\<^sub>2 x A' = ((return M x) \<star> N) A'" if "x \<in> space M" for A' x
    unfolding K\<^sub>2_def
    apply (cases "A' \<in> sets M")
    apply auto defer
    apply (simp add: assms(4) assms(5) emeasure_notin_sets)
    apply (subst kernel_apply_kernel_of)
    using that kernel_apply_kernel_of apply auto
    apply (rule transition_kernelI)
    sorry
  have "(\<lambda>x. emeasure N A') \<in> borel_measurable N" if "A' \<in> sets N" for A'
    unfolding measurable_def by auto
  moreover have "{a. a + x \<in> A'} \<in> sets N" if "A' \<in> sets N" for A' x
    using that apply measurable
    unfolding pred_def using that assms(4) sorry
  ultimately have *: "(\<lambda>x. emeasure N {a. a + x \<in> A'}) \<in> borel_measurable N" if "A' \<in> sets N" for A'
    using that sorry
  have int_eq: "(\<integral>\<^sup>+ x. emeasure (return M x \<star> N) A' \<partial>M) = (emeasure (M \<star> N) A')" if "A' \<in> sets M" for A'
    apply (subst convolution_emeasure)
           apply (simp_all add: that assms)
    using assms(4) assms(5) that apply blast
        apply (simp add: assms(4) assms(5) prob_space.finite_measure prob_space_return sets_eq_imp_space_eq)
       apply (simp add: assms(2) prob_space.finite_measure)
      apply (simp add: assms(4) assms(5) sets_eq_imp_space_eq)
     apply (simp add: assms(4) sets_eq_imp_space_eq)
    apply (subst nn_integral_return)
      apply (simp add: assms(4) assms(5) sets_eq_imp_space_eq)
    using assms that apply measurable
     defer
     apply (metis assms(1) assms(2) assms(4) assms(5) convolution_emeasure prob_space.finite_measure sets_eq_imp_space_eq that)
    using * that assms(5) by simp
  show ?thesis
  apply (subst kernel_comp_kernel)
  using K\<^sub>1_def K\<^sub>2_def apply simp
  using K\<^sub>1_def assms(1)
   apply (metis emeasure_transition_kernel finite_kernelI kernel_apply_kernel_of
      kernel_measure_emeasure kernel_measure_space prob_space.emeasure_space_1
      prob_space.finite_measure prob_spaceI sets.top source_kernel_of target_kernel_of)
  apply (auto simp add: fun_eq_iff K1_measure)
  subgoal for A'
    apply (subst nn_integral_cong[of M "\<lambda>x. (kernel K\<^sub>2 x A')" "(\<lambda>x. ((return M x) \<star> N) A')"])
    using K2 apply blast
    apply (cases "A' \<in> sets M")
    using int_eq apply blast
     apply (smt (verit, best) assms(4) assms(5) emeasure_neq_0_sets mult_zero_left nn_integral_cong nn_integral_const sets_convolution)
    done
  done
qed


end