theory Brownian_Motion
  imports Continuous_Modification Markov_Semigroup
begin

text \<open> I am trying to prove the existence of a Wiener process with continuous paths.
  The issue is that Kolmogorov's theorem does not guarantee continuity - it merely proves the
  existence of a process with given finite-dimensional distributions. 
  Our statement of Kolmogorov's theorem is the following \<close>

thm polish_projective.emeasure_lim_emb

text \<open> For any projective (i.e. consistent) family of finite-dimensional distributions in a polish 
  space, we can define a probability measure lim on paths which agrees on all finite-dimensional
  distributions.

  Then, the coordinate mappings form a real-valued stochastic process with the prescribed distributions \<close>


context polish_projective
begin

lemma "i \<in> I \<Longrightarrow> (\<lambda>x. x i) \<in> lim \<rightarrow>\<^sub>M borel"
  by (simp add: measurable_def)

end

text \<open> Adapting @{thm conv_normal_density_zero_mean} for the convolution operator \<close>
theorem convolution_normal_density_zero_mean:
  assumes geq[arith, simp]: "s > 0" "t > 0"
  shows "(density lborel (normal_density 0 s)) \<star> (density lborel (normal_density 0 t)) 
        = (density lborel (normal_density 0 (sqrt (s\<^sup>2 + t\<^sup>2))))"
  apply (subst convolution_density)
      apply measurable
  apply (simp_all add: prob_space.finite_measure prob_space_normal_density)
  apply (rule density_cong)
    apply measurable
   apply (auto simp: ennreal_mult[THEN sym])
  using conv_normal_density_zero_mean[OF geq] fun_eq_iff apply fast
  done

interpretation finite_measure_return: finite_measure "return M x"
  apply (intro finite_measureI)
  apply (cases "x \<in> space M")
  by auto

text \<open> Ill-defined for i < 0 \<close>

text_raw \<open>\DefineSnippet{Wiener_kernel{\<close>
definition Wiener_kernel :: "real \<Rightarrow> real hkernel" where
"Wiener_kernel i \<equiv> if i = 0 then hkernel (return_kernel borel)
   else hkernel_of borel (\<lambda>x dy. (return borel x \<star> density lborel (normal_density 0 i)) dy)"
text_raw\<open>}%EndSnippet\<close>

lemma Wiener_kernel_0: "Wiener_kernel 0 = return_kernel borel"
  unfolding Wiener_kernel_def by (simp add: from_hkernel_inverse)

lemma transition_kernel_Wiener:
  assumes "i > 0"
  shows "transition_kernel borel borel (\<lambda>x dy. (return borel x \<star> density lborel (normal_density 0 i)) dy)"
  apply (rule transition_kernel.intro)
   apply (subst convolution_emeasure)
          apply auto
     apply (simp add: subprob_space.axioms(1) subprob_space_return_ne)
  using prob_space.finite_measure prob_space_normal_density assms apply blast
   apply (subst measurable_cong[OF nn_integral_return])
     apply measurable
    apply (simp_all add: measurable_cong[OF emeasure_density])
  by (metis measure_space sets_convolution space_borel space_convolution)

lemma kernel_Wiener:
  assumes "i \<ge> 0" "A \<in> sets borel"
  shows "kernel (Wiener_kernel i) \<omega> A = 
      (if i = 0 then return borel \<omega> A
       else (return borel \<omega> \<star> density lborel (normal_density 0 i)) A)"
  using assms unfolding Wiener_kernel_def apply (simp add: transition_kernel_Wiener)
  apply (transfer, auto)
  by (auto simp: transition_kernel_Wiener return_kernel_def from_hkernel_inverse)

interpretation Wiener_kernel_semigroup: markov_semigroup Wiener_kernel borel
proof (intro markov_semigroup.intro, goal_cases)
  case (1 i)
  then show ?case
    unfolding Wiener_kernel_def 
    by (auto simp: from_hkernel_inverse return_kernel_def)
next
  case (2 \<omega>)
  then show ?case
    apply (simp add: Wiener_kernel_0)
    by (metis hkernel_of.rep_eq hkernel_of_space kernel_measure_kernel_of measure_of_of_measure
        return_kernel return_kernel_def sets_return space_return)
next
  case (3 s t)
  then show ?case
    unfolding kernel_comp_def Wiener_kernel_def
    apply auto
       apply (rule transition_kernel_eq_iff)
         apply simp_all
    sorry
next
  case (4 i)
  then show ?case sorry
qed

definition brownian_motion_measure where
"brownian_motion_measure \<equiv>
   distr (return borel 0 \<Otimes>\<^sub>S Wiener_kernel_semigroup.lim_kernel) (PiM {0..} (\<lambda>_. borel)) (\<lambda>(x,y). y(0:=x))"

interpretation brownian_motion_prob: prob_space brownian_motion_measure
  sorry

definition brownian_motion_process where
"brownian_motion_process \<equiv> brownian_motion_prob.process_of borel {0..} (\<lambda>i \<omega>. \<omega> i) 0"

text_raw \<open>\DefineSnippet{brownian_motion}{\<close>
locale brownian_motion =
  fixes W :: "(real, 'a, real) stochastic_process"
  assumes init_0[simp]: "\<P>(x in proc_source W. W 0 x = 0) = 1"
      and indep_increments: "indep_increments W"
      and normal_increments: "\<And>s t. 0 \<le> s \<and> s < t \<Longrightarrow>
   distributed (proc_source W) borel (\<lambda>v. W t v - W s v) (normal_density 0 (sqrt (t-s)))"
      and AE_continuous: "AE x in proc_source W. continuous_on {0..} (\<lambda>t. W t x)"
text_raw\<open>}%EndSnippet\<close>

lemma brownian_motion_process: "brownian_motion brownian_motion_process"
proof (intro brownian_motion.intro, goal_cases)
  case 1
  then show ?case sorry
next
  case 2
  then show ?case sorry
next
  case (3 s t)
  then show ?case sorry
next
  case 4
  then show ?case sorry
qed

(*
context brownian_motion
begin

lemma stationary_Wiener: "stationary_increments lborel W"
  unfolding stationary_increments_def
proof auto
  fix t1 t2 k :: real
  assume "t1 > 0" "t2 > 0" "k > 0"
  then have "distributed M lborel (\<lambda>v. W (t1 + k) v - W t1 v) (normal_density 0 (sqrt k))"
    using normal_increments[of "t1" "t1 + k"] by simp
  moreover have "distributed M lborel (\<lambda>v. W (t2 + k) v - W t2 v) (normal_density 0 (sqrt k))"
    using normal_increments[of "t2" "t2 + k"] \<open>0 < k\<close> \<open>0 < t2\<close> by simp
  ultimately show "distr M lborel (\<lambda>v. W (t1 + k) v - W t1 v) = distr M lborel (\<lambda>v. W (t2 + k) v - W t2 v)"
    unfolding distributed_def by argo
qed

lemma indep_var_Wiener:
  assumes "0 \<le> s" "s \<le> t"
  shows "indep_var borel (W s) borel (\<lambda>x. W t x - W s x)"
proof -
  have "indep_var borel (\<lambda>x. W s x - W 0 x) borel (\<lambda>x. W t x - W s x)"
    using assms indep_increments indep_increments_indep_var by fastforce
  then show ?thesis
    by simp
qed

lemma Wiener_distributed_t: "t > 0 \<Longrightarrow> distributed M lborel (W t) (normal_density 0 (sqrt t))"
proof -
  assume "t > 0"
  then have 1: "distributed M lborel (\<lambda>v. W t v - W 0 v) (normal_density 0 (sqrt t))"
    using normal_increments[of 0 t] by simp
  have "AE x in M. (\<lambda>v. W t v - W 0 v) x = W t x"
    using init_0 AE_prob_1 by force
  then have "distr M lborel (\<lambda>v. W t v - W 0 v) = distr M lborel (W t)"
    by (intro distr_cong_AE; simp add: random_X)
  then show "distributed M lborel (W t) (normal_density 0 (sqrt t))"
    using 1 unfolding distributed_def by simp
qed

lemma Wiener_expectation: "t \<ge> 0 \<Longrightarrow> expectation (W t) = 0"
proof -
  have exp_0: "expectation (W 0) = 0"
    by (simp add: integral_eq_zero_AE)
  moreover {
    assume *: "t > 0"
    then have "distributed M lborel (W t) (normal_density 0 (sqrt t))"
      by (rule Wiener_distributed_t)
    then have "expectation (W t) = 0"
      using "*" normal_distributed_expectation real_sqrt_gt_0_iff by blast
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> expectation (W t) = 0"
    by fastforce
qed

lemma Wiener_variance:"t \<ge> 0 \<Longrightarrow> variance (W t) = t"
proof -
  have "variance (W 0) = 0"
    by (simp add: integral_eq_zero_AE)
  moreover {
    assume "t > 0"
    then have "sqrt t > 0"
      by simp
    then have "variance (W t) = sqrt t ^ 2"
      using normal_distributed_variance \<open>0 < t\<close> Wiener_distributed_t by blast
    also have "... = t"
      using \<open>0 < t\<close> by auto
    finally have ?thesis .
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> variance (W t) = t"
    by (cases "t > 0"; auto)
qed

theorem integrable_W: "t \<ge> 0 \<Longrightarrow> integrable M (W t)"
proof -
  have "has_bochner_integral M (W 0) 0"
    by (simp add: has_bochner_integral_cong has_bochner_integral_zero)
  then have "integrable M (W 0)"
    using integrable.simps by blast
  moreover {
    assume *: "t > 0"
    then have "distributed M lborel (W t) (normal_density 0 (sqrt t))"
      by (fact Wiener_distributed_t)
    then have ?thesis
      by (simp add: "*" distributed_integrable_var integrable_normal_moment_nz_1)
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> integrable M (W t)"
    by fastforce
qed

lemma integrable_W_squared: "t \<ge> 0 \<Longrightarrow> integrable M (\<lambda>x. (W t x)\<^sup>2)"
proof -
  have "has_bochner_integral M (\<lambda>x. (W 0 x)\<^sup>2) 0"
    by (simp add: has_bochner_integral_zero)
  moreover {
    assume "t > 0"
    then have "sqrt t > 0"
      by simp
    then have "integrable lborel (\<lambda>x. normal_density 0 (sqrt t) x * x\<^sup>2)"
      using integrable_normal_moment[of "sqrt t" 0 2] by simp
    then have ?thesis
      apply (subst distributed_integrable[where g="\<lambda>x. x\<^sup>2" and N = lborel and f="normal_density 0 (sqrt t)", symmetric])
      using Wiener_distributed_t \<open>0 < t\<close> apply blast
      by auto
  }
  ultimately show "t \<ge> 0 \<Longrightarrow> ?thesis"
    using integrable.simps less_eq_real_def by blast
qed

lemma Wiener_expectation_prod_le:
  assumes "0 \<le> s" "s \<le> t"
  shows "expectation (\<lambda>x. W s x * W t x) = s"
proof -
  have "indep_var borel (W s) borel (\<lambda>x. W t x - W s x)"
    using assms indep_var_Wiener by blast
  then have "integrable M (\<lambda>x. W s x * (W t x - W s x))"
    using integrable_W assms indep_var_integrable[of "W s" "(\<lambda>x. W t x - W s x)"] by auto
  moreover have "integrable M (\<lambda>x. (W s x)\<^sup>2)"
    by (simp add: assms(1) integrable_W_squared)
  moreover have "(\<lambda>x. W s x * W t x) = (\<lambda>x. W s x * (W t x - W s x) + W s x ^ 2)"
    by (simp add: fun_eq_iff power2_eq_square right_diff_distrib)
  ultimately have "expectation (\<lambda>x. W s x * W t x) = expectation (\<lambda>x. W s x * (W t x - W s x)) + expectation (\<lambda>x. W s x ^ 2)"
    by simp
  also have "... = expectation (W s) * expectation (\<lambda>x. W t x - W s x) + expectation (\<lambda>x. W s x ^ 2)"
    using indep_var_Wiener[OF assms] indep_var_lebesgue_integral apply auto
    using assms indep_var_lebesgue_integral brownian_motion.integrable_W brownian_motion_axioms by fastforce
  also have "... = expectation (\<lambda>x. W s x ^ 2)"
    using Wiener_expectation assms(1) by simp
  also have "... = s"
    using Wiener_variance
    by (simp add: Wiener_variance Wiener_expectation assms(1))
  finally show ?thesis .
qed

corollary Wiener_expectation_prod: 
  assumes "s \<ge> 0" "t \<ge> 0"
  shows "expectation (\<lambda>x. W s x * W t x) = min s t"
  apply (cases "s \<le> t")
    apply (simp add: Wiener_expectation_prod_le assms(1))
    apply (subst mult.commute, simp add: Wiener_expectation_prod_le assms(2))
  done

lemma Wiener_distributions_emeasure:
  assumes "J \<subseteq> {0..}" "finite J" "X \<in> sets (\<Pi>\<^sub>M i\<in>J. borel)"
  shows "distributions J X = undefined"
  sorry

lemma Wiener_lim:
  assumes "J \<subseteq> {0..}" "finite J" "X \<in> sets (\<Pi>\<^sub>M i\<in>J. borel)"
  shows "lim (emb {0..} J X) = distributions J X"
  using assms emeasure_lim_emb by presburger

lemma Wiener_PiM_density: (* distribution given by 37.6 in Billingsley *)
  assumes "sorted ls" "length ls \<ge> 2" "set ls \<subseteq> {0..}"
  shows "distributed M lborel (W t) (normal_density 0 (sqrt t))"
  oops
end

theorem (in prob_space) Wiener_scale_invariant:
  assumes "brownian_motion M W"
  shows "stochastic_process.distributions M borel W = 
        stochastic_process.distributions M borel (\<lambda>t x. 1/(sqrt c) * W (c*t) x)"n 
  oops
*)
end
