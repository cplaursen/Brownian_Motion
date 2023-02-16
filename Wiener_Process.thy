theory Wiener_Process
  imports Stochastic_Process
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

text \<open> Adaptation @{thm conv_normal_density_zero_mean} for the convolution operator \<close>
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
definition Wiener_kernel :: "real \<Rightarrow> real hkernel" where
"Wiener_kernel i \<equiv> hkernel (if i = 0 then kernel_of borel borel (return borel)
   else kernel_of borel borel (\<lambda>x dy. (return borel x \<star> density lborel (normal_density 0 i)) dy))"

lemma Wiener_kernel_0: "kernel (Wiener_kernel 0) x A' = (\<lambda>x. emeasure (return borel x)) x A'"
  unfolding Wiener_kernel_def 
  by (cases "A' \<in> sets borel"; simp add: emeasure_notin_sets)

lemma transition_kernel_Wiener:
  assumes "i > 0"
  shows "transition_kernel borel borel (\<lambda>x dy. (return borel x \<star> density lborel (normal_density 0 i)) dy)"
  apply (rule transition_kernelI)
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
  using assms unfolding Wiener_kernel_def by (simp add: transition_kernel_Wiener)

interpretation markov_semigroup Wiener_kernel borel
  unfolding Wiener_kernel_def apply (intro markov_semigroup.intro)
    apply auto
    apply (rule measure_eqI)
     apply auto
        apply (simp add: kernel_measure_emeasure)
  sorry

end