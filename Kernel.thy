theory Kernel
  imports "HOL-Probability.Probability"
begin

section \<open> Transition kernel locale \<close>

text \<open> Let M and M' be measure spaces. A (\<sigma>-) finite transition kernel is a map
   K :: (space M) => (sets M') => ennreal, which satisfies the following conditions:

  \<omega> -> K \<omega> A' is M-measurable (w.r.t. borel - Not in the textbook) for any A' in sets M'
  A' -> K \<omega> A' is a (\<sigma>-) finite measure on M' for any \<omega> in space M \<close>

text \<open> A stochastic transition kernel can be understood as the generalisation of a transition matrix
  for Markov chains. In this analogy, a transition kernel maps the current state \<omega> to a probability
  distribution over possible future state. Indeed, when restricted to a countable state space the
  two definitions coincide. \<close>

text_raw \<open>\DefineSnippet{transition_kernel}{\<close>
locale transition_kernel =
  fixes M :: "'a measure"
    and M' :: "'b measure"
    and \<kappa> :: "'a \<Rightarrow> 'b set \<Rightarrow> ennreal"
  assumes
    sets_target_measurable [measurable]: "\<And>A'. A' \<in> sets M' \<Longrightarrow> (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel" and
    space_source_measure: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> measure_space (space M') (sets M') (\<lambda>A'. \<kappa> \<omega> A')"
text_raw \<open>}%EndSnippet\<close>

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

lemma transition_kernel_cong_sets:
  assumes "sets M = sets N" "sets M' = sets N'"
    "\<And>\<omega> A'. \<omega> \<in> space M \<Longrightarrow> A' \<in> sets M' \<Longrightarrow> f \<omega> A' = g \<omega> A'"
  shows "transition_kernel M M' f = transition_kernel N N' g"
proof -
  {
    fix f g :: "'a \<Rightarrow> 'b set \<Rightarrow> ennreal"
    assume eq: "\<And>\<omega> A'. \<omega> \<in> space M \<Longrightarrow> A' \<in> sets M' \<Longrightarrow> f \<omega> A' = g \<omega> A'"
       and f: "transition_kernel M M' f"
    then have "A' \<in> sets N' \<Longrightarrow> (\<lambda>\<omega>. g \<omega> A') \<in> borel_measurable N" for A'
      apply (subst measurable_cong[where g="\<lambda>\<omega>. f \<omega> A'"])
       using assms apply (metis sets_eq_imp_space_eq)
       unfolding transition_kernel_def using assms by auto
     moreover have "\<omega> \<in> space N \<Longrightarrow> measure_space (space N') (sets N') (g \<omega>)" for \<omega>
       by (metis assms(1) assms(2) eq f measure_space_eq sets.sigma_sets_eq sets.space_closed
           sets_eq_imp_space_eq transition_kernel.space_source_measure)
     ultimately have "transition_kernel N N' g"
       unfolding transition_kernel_def by presburger
  }
  then show ?thesis
    by (smt (verit) assms measurable_cong_sets sets_eq_imp_space_eq transition_kernel_def)
qed

lemma transition_kernel_cong: 
  assumes "\<And>\<omega> A'. \<omega> \<in> space M \<Longrightarrow> A' \<in> sets M' \<Longrightarrow> f \<omega> A' = g \<omega> A'"
  shows "transition_kernel M M' f = transition_kernel M M' g"
  using assms transition_kernel_cong_sets by blast

text \<open> Klenke remark 8.26 \<close>
lemma kernel_measurable_pi_system:
  assumes measurable_P[measurable]: "\<And>A'. A' \<in> P \<Longrightarrow> (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel" and
    P: "Int_stable P" "space M' \<in> P" "sigma_sets (space M') P = sets M'" and
    measure_space: "\<And>\<omega>. \<omega> \<in> space M \<Longrightarrow> measure_space (space M') (sets M') (\<kappa> \<omega>)"
  shows "transition_kernel M M' \<kappa>"
proof
  show "\<And>A'. A' \<in> sets M' \<Longrightarrow> (\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel"
  proof -
    fix A' assume A': "A' \<in> sets M'"
    have "P \<subseteq> Pow (space M')"
      using P(3) sets.space_closed by blast
    moreover have "A' \<in> sigma_sets (space M') P"
      using P(3) A' by blast
    with P(1) calculation
    show "(\<lambda>\<omega>. \<kappa> \<omega> A') \<in> M \<rightarrow>\<^sub>M borel"
    proof (induct rule: sigma_sets_induct_disjoint)
      case (basic A)
      then show ?case by simp
    next
      case empty
      then show ?case
        apply (subst measurable_cong[where g="\<lambda>x. 0"])
        using measure_space apply (simp add: Sigma_Algebra.positive_def measure_space_def)
        apply simp
        done
    next
      case (compl A)
      then show ?case
        sorry (* K \<omega> A needs to be finite for this to hold, it seems *)
    next
      case (union A)
      then show ?case sorry
    qed
  qed
qed (fact measure_space)

text \<open> Adapted version of emeasure_distr to work with measure spaces \<close>
lemma measure_space_distr:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes f: "f \<in> measurable M N"
      and measure_space:"measure_space (space M) (sets M) \<mu>"
  shows "measure_space (space N) (sets N) (\<lambda>A. \<mu> (f -` A \<inter> space M))"
proof (unfold measure_space_def, safe)
  show "positive (sets N) (\<lambda>A. \<mu> (f -` A \<inter> space M))"
    using measure_space by (auto simp: positive_def measure_space_def)
  show "countably_additive (sets N) (\<lambda>A. \<mu> (f -` A \<inter> space M))"
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> 'b set" assume "range A \<subseteq> sets N" "disjoint_family A"
    then have "\<And>i. A i \<in> sets N" "(\<Union>i. A i) \<in> sets N"
      by auto
    then have *: "range (\<lambda>i. f -` (A i) \<inter> space M) \<subseteq> sets M"
      using f by (auto simp: measurable_def)
    moreover have "(\<Union>i. f -`  A i \<inter> space M) \<in> sets M"
      using * by blast
    moreover have **: "disjoint_family (\<lambda>i. f -` A i \<inter> space M)"
      using \<open>disjoint_family A\<close> by (auto simp: disjoint_family_on_def)
    ultimately show "(\<Sum>i. \<mu> (f -` A i \<inter> space M)) = \<mu> (f -` \<Union> (range A) \<inter> space M)"
      using assms(2) by (auto simp: countably_additive_def measure_space_def vimage_UN)
  qed
  show "sigma_algebra (space N) (sets N)"
    by (fact sets.sigma_algebra_axioms)
qed

lemma (in transition_kernel) transition_kernel_distr:
  assumes  f[measurable]: "f \<in> M' \<rightarrow>\<^sub>M N'"
    shows "transition_kernel M N' (\<lambda>\<omega> A'. \<kappa> \<omega> (f -` A' \<inter> space M'))"
proof
  fix A' assume "A' \<in> sets N'"
  then have "f -` A' \<inter> space M' \<in> sets M'"
    by measurable
  then show "(\<lambda>\<omega>. \<kappa> \<omega> (f -` A' \<inter> space M')) \<in> borel_measurable M"
    using sets_target_measurable by blast
next
  fix \<omega> assume "\<omega> \<in> space M"
  then have "measure_space (space M') (sets M') (\<lambda>A'. \<kappa> \<omega> A')"
    by (simp add: space_source_measure)
  with f show "measure_space (space N') (sets N') (\<lambda>A'. \<kappa> \<omega> (f -` A' \<inter> space M'))"
    by (rule measure_space_distr)
qed

section \<open> Kernel type \<close>
text \<open> The boilerplate definitions for the kernel type follow closely those of the measure type
   @{typ "'a measure"}\<close>

text_raw \<open>\DefineSnippet{kernel}{\<close>
typedef ('a, 'b) kernel =
  "{(M :: 'a measure, M' :: 'b measure, \<kappa>). 
    transition_kernel M M' \<kappa> \<and> (\<forall>\<omega>. \<forall>A'. \<omega> \<in> -space M \<or> A' \<in> -sets M' \<longrightarrow> \<kappa> \<omega> A' = 0)}"
text_raw \<open>}%EndSnippet\<close>
  using transition_kernel_zero by blast

setup_lifting type_definition_kernel

lift_definition kernel_source :: "('a, 'b) kernel \<Rightarrow> 'a measure" is fst .

lift_definition kernel_target :: "('a, 'b) kernel \<Rightarrow> 'b measure" is "fst \<circ> snd" .

lift_definition kernel :: "('a, 'b) kernel \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> ennreal" is "snd \<circ> snd" .

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

lemma transition_kernel_eq_iff:
  assumes "kernel_source K = kernel_source L" "kernel_target K = kernel_target L" "kernel K = kernel L"
  shows "K = L"
  using assms by (transfer, force)

lift_definition kernel_of :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a \<Rightarrow> 'b set \<Rightarrow> ennreal) \<Rightarrow> ('a, 'b) kernel"
  is"\<lambda>M M' \<kappa>. (M, M', \<lambda>\<omega> A'. if \<omega> \<in> space M \<and> A' \<in> sets M' \<and> transition_kernel M M' \<kappa>
                             then \<kappa> \<omega> A' else 0)"
  subgoal for M M' \<kappa>
    by (cases "transition_kernel M M' \<kappa>") auto
  done
                                                                 
lemma source_kernel_of [simp]: "kernel_source (kernel_of M M' \<kappa>) = M"
  by (transfer, auto)

lemma target_kernel_of [simp]: "kernel_target (kernel_of M M' \<kappa>) = M'"
  by (transfer, auto)

lemma kernel_apply_kernel_of [simp]:
  assumes "\<omega> \<in> space M" "A' \<in> sets M'" "transition_kernel M M' \<kappa>"
  shows "kernel (kernel_of M M' \<kappa>) \<omega> A' = \<kappa> \<omega> A'"
  using assms by (transfer, auto)

text \<open> Homogeneous kernel \<close>
typedef 'a hkernel = "{K :: ('a, 'a) kernel. kernel_source K = kernel_target K}"
  morphisms from_hkernel hkernel
  by (simp, metis source_kernel_of target_kernel_of)

setup_lifting type_definition_hkernel

declare [[coercion from_hkernel]]

lift_definition hkernel_space :: "'a hkernel \<Rightarrow> 'a measure" is kernel_source .

lemma hkernel_source_eq_target: 
  "kernel_source (from_hkernel K) = kernel_target (from_hkernel K)"
  using from_hkernel by auto

lemma from_hkernel_kernel_of_inverse [simp]:
  "from_hkernel (hkernel (kernel_of M M \<kappa>)) = (kernel_of M M \<kappa>)"
  by (simp add: hkernel_inverse)

lift_definition hkernel_of :: "'a measure \<Rightarrow> ('a \<Rightarrow> 'a set \<Rightarrow> ennreal) \<Rightarrow> 'a hkernel"
  is "\<lambda>M \<kappa>. kernel_of M M \<kappa>"
  by simp

lemma hkernel_of_space[simp]: "hkernel_space (hkernel_of M \<kappa>) = M"
  by (transfer, auto)

lemma hkernel_space_hkernel [simp]:
  assumes "kernel_source K = kernel_target K"
  shows "hkernel_space (hkernel K) = kernel_source K"
  using assms by (simp add: hkernel_inverse hkernel_space.rep_eq)

lemma kernel_source_from_hkernel [simp]: "kernel_source (from_hkernel K) = hkernel_space K"
  by (transfer, simp)

lemma kernel_target_from_hkernel [simp]: "kernel_target (from_hkernel K) = hkernel_space K"
  by (transfer, simp)

lemma hkernel_of_kernel [simp]:
  assumes "\<omega> \<in> space M" "A' \<in> sets M" "transition_kernel M M K"
  shows "kernel (hkernel_of M K) \<omega> A' = K \<omega> A'"
  using assms by (transfer, auto)

text_raw \<open>\DefineSnippet{kernel_measure}{\<close>
lift_definition kernel_measure :: "('a, 'b) kernel \<Rightarrow> 'a \<Rightarrow> 'b measure" is
"\<lambda>(M, M', \<kappa>) \<omega>. measure_of (space M') (sets M') (\<lambda>A'. \<kappa> \<omega> A')"
text_raw \<open>}%EndSnippet\<close> .

lemma kernel_measure_altdef:
  "kernel_measure K \<omega> = measure_of (space (kernel_target K)) (sets (kernel_target K)) (\<lambda>A'. K \<omega> A')"
  by (transfer, auto)

lemma kernel_measure_space [simp]: "space (kernel_measure K \<omega>) = space (kernel_target K)"
  by (transfer, auto)

lemma kernel_measure_sets [simp]: "sets (kernel_measure K \<omega>) = sets (kernel_target K)"
  by (transfer, auto)

lemma kernel_measure_emeasure[simp]: "emeasure (kernel_measure K \<omega>) = kernel K \<omega>"
  apply (rule ext)
  subgoal for A'
    apply (cases "\<omega> \<in> space (kernel_source K) \<and> A' \<in> sets (kernel_target K)")
     apply (transfer, auto)[1]
     apply (meson emeasure_measure_of_sigma sets.sigma_algebra_axioms
                 transition_kernel.countably_additive transition_kernel.positive)
    apply (transfer, auto)
     apply (metis emeasure_measure_of_conv)
    using emeasure_neq_0_sets sets.sets_measure_of_eq apply blast
    done
  done

lemma kernel_measure_notin_space:
  assumes "\<omega> \<notin> space (kernel_source K)"
  shows "kernel_measure K \<omega> = measure_of (space (kernel_target K)) (sets (kernel_target K)) (\<lambda>_. 0)"
  using assms apply (transfer, auto)
  by presburger

lemma measurable_kernel_measure: "(f \<in> (kernel_measure K \<omega>) \<rightarrow>\<^sub>M M) = (f \<in> (kernel_target K) \<rightarrow>\<^sub>M M)"
  by (auto simp: measurable_cong_sets[of "kernel_measure K \<omega>" "kernel_target K" M M])

lemma kernel_measure_kernel_of:
  assumes "\<omega> \<in> space M" "transition_kernel M M' \<kappa>"
  shows "kernel_measure (kernel_of M M' \<kappa>) \<omega> = measure_of (space M') (sets M') (\<lambda>A'. \<kappa> \<omega> A')"
  using assms apply transfer
    apply simp
    apply (intro measure_of_eq)
      using sets.space_closed apply blast
      using sets.sigma_sets_eq apply auto
      done

lemma sets_kernel_measureI[measurable(raw)]: "A \<in> sets (kernel_target K) \<Longrightarrow> A \<in> sets (kernel_measure K \<omega>)"
  by (metis kernel_measure_sets)

lemma measurable_kernel_measureI[measurable(raw)]: 
  "f \<in> kernel_target K \<rightarrow>\<^sub>M M \<Longrightarrow> f \<in> kernel_measure K \<omega> \<rightarrow>\<^sub>M M"
  by (meson measurable_kernel_measure)

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
  shows "K \<omega> A \<noteq> \<top>"
proof (cases "\<omega> \<in> space (kernel_source K)")
  case False
  then show ?thesis by simp
next
  case True
  then have "finite_measure (kernel_measure K \<omega>)"
    by (simp add: finite_kernel.finite_measures assms)
  then have "emeasure (kernel_measure K \<omega>) A \<noteq> \<top>"
    by (metis finite_measure.emeasure_finite)
  then show "K \<omega> A \<noteq> \<top>"
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

lemma stochastic_kernel_altI:
  assumes "\<And>\<omega>. \<omega> \<in> space (kernel_source K) \<Longrightarrow> K \<omega> (space (kernel_target K)) = 1"
  shows "stochastic_kernel K"
  apply (intro stochastic_kernelI prob_spaceI)
  by (simp add: assms)

lemma (in stochastic_kernel) kernel_space_eq_1 [simp]:
  assumes "\<omega> \<in> space (kernel_source K)"
  shows "K \<omega> (space (kernel_target K)) = 1"
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

lemma kernel_of_cong:
  assumes "\<And>\<omega> A'. \<omega> \<in> space M \<and> A' \<in> sets M' \<Longrightarrow> \<kappa> \<omega> A' = \<kappa>' \<omega> A'"
  shows "kernel_of M M' \<kappa> = kernel_of M M' \<kappa>'"
  using assms apply (transfer, auto simp add: fun_eq_iff)
  unfolding transition_kernel_def
   apply (smt (verit, best) measurable_cong measure_space_eq sets.sigma_sets_eq sets.space_closed)+
  done

text \<open> Klenke lemma 14.23 \<close>

text_raw \<open>\DefineSnippet{kernel_measure_pair_integral_measurable}{\<close>
lemma kernel_measure_pair_integral_measurable [measurable]:
  fixes f :: "'a \<times> 'b \<Rightarrow> ennreal"
    and K :: "('a, 'b) kernel"
  assumes f_measurable[measurable]: "f \<in> borel_measurable (kernel_source K \<Otimes>\<^sub>M kernel_target K)"
      and finite_K: "finite_kernel K"
  defines "I \<equiv> \<lambda> f. (\<lambda>\<omega>\<^sub>1. \<integral>\<^sup>+\<omega>\<^sub>2. f(\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1)"
  shows "I f \<in> borel_measurable (kernel_source K)"
text_raw \<open>}%EndSnippet\<close>
proof -
  let ?\<Omega>\<^sub>1 = "space (kernel_source K)" and ?\<Omega>\<^sub>2 = "space (kernel_target K)"
  and ?A\<^sub>1 = "sets (kernel_source K)"  and ?A\<^sub>2 = "sets (kernel_target K)"
  have f_snd_measurable[measurable]: "(\<lambda>\<omega>\<^sub>2. f (\<omega>\<^sub>1, \<omega>\<^sub>2)) \<in> borel_measurable (kernel_target K)"
    if "\<omega>\<^sub>1 \<in> space (kernel_source K)" for \<omega>\<^sub>1
    using that by measurable
  have I_pair_measurable[measurable]: "I (indicator (X \<times> Y)) \<in> borel_measurable (kernel_source K)"
    if "X \<in> ?A\<^sub>1" "Y \<in> ?A\<^sub>2" for X Y
  proof -
    have "I (indicator (X \<times> Y)) = (\<lambda>\<omega>\<^sub>1. indicator X \<omega>\<^sub>1 * kernel K \<omega>\<^sub>1 Y)"
      unfolding I_def apply (subst nn_integral_eq_simple_integral)
      using that by (transfer, auto simp: indicator_times)
    also have "... \<in> borel_measurable (kernel_source K)"
      using that by measurable
    finally show ?thesis .
  qed
  let ?G = "{a \<times> b | a b. a \<in> ?A\<^sub>1 \<and> b \<in> ?A\<^sub>2}"
  have sigma_G: "sigma_sets (space (kernel_source K \<Otimes>\<^sub>M kernel_target K)) ?G =
                 sets (kernel_source K \<Otimes>\<^sub>M kernel_target K)"
    by (simp add: sets_pair_measure space_pair_measure)
  have "Int_stable ?G"
    using Int_stable_pair_measure_generator by blast
  moreover have "?G \<subseteq> Pow (space (kernel_source K \<Otimes>\<^sub>M kernel_target K))"
    by (simp add: pair_measure_closed space_pair_measure)
  ultimately have [measurable]: "I (indicator A) \<in> borel_measurable (kernel_source K)"
    if \<open>A \<in> sigma_sets (space (kernel_source K \<Otimes>\<^sub>M kernel_target K)) ?G\<close> for A
  using that
  proof (induction rule: sigma_sets_induct_disjoint)
    case (basic A)
    then obtain X Y where XY: "X \<in> ?A\<^sub>1" "Y \<in> ?A\<^sub>2" "A = X \<times> Y"
      by blast
    show ?case
      using XY(1,2) by (subst XY(3), measurable) 
  next
    case empty
    then show ?case
       unfolding I_def by force
  next
    case (compl A)
    then have [measurable]: "A \<in> sets (kernel_source K \<Otimes>\<^sub>M kernel_target K)"
      using sigma_G by blast
    from compl have "(\<lambda>\<omega>\<^sub>1. I (indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)) \<omega>\<^sub>1 - I (indicator A) \<omega>\<^sub>1) \<in> borel_measurable (kernel_source K)"
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
          using \<omega>\<^sub>1 finite_K finite_kernel.finite_measures finite_measure.finite_emeasure_space
            top.not_eq_extremum by fastforce
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
        using \<omega>\<^sub>1 kernel_measure_sets apply measurable
        using finite_integral apply simp
        using \<omega>\<^sub>1 by fastforce
      finally show "I (indicator ((?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2) - A)) \<omega>\<^sub>1 = I (indicator (?\<Omega>\<^sub>1 \<times> ?\<Omega>\<^sub>2)) \<omega>\<^sub>1 - I (indicator A) \<omega>\<^sub>1"
        unfolding I_def .
    qed
    ultimately show ?case
      by (subst measurable_cong, auto simp: space_pair_measure)
  next
    case (union A)
    then have "A i \<in> sets (kernel_source K \<Otimes>\<^sub>M kernel_target K)" for i
      by (simp add: sigma_G)
    then have [measurable]: "indicator (A i) \<in> borel_measurable (kernel_source K \<Otimes>\<^sub>M kernel_target K)" for i
      using borel_measurable_indicator by blast
      have "\<And>\<omega>\<^sub>1. \<omega>\<^sub>1 \<in> ?\<Omega>\<^sub>1 \<Longrightarrow> I (indicator (\<Union> (range A))) \<omega>\<^sub>1 = (\<Sum>n. I (indicator (A n)) \<omega>\<^sub>1)"
        unfolding I_def
        apply (subst suminf_indicator[THEN sym])
        using union apply auto[1]
        apply (rule nn_integral_suminf)
        by measurable
    moreover have "(\<lambda>\<omega>\<^sub>1. \<Sum>n. I (indicator (A n)) \<omega>\<^sub>1) \<in> borel_measurable (kernel_source K)"
      apply measurable
      using union by blast
    ultimately show "I (indicator (\<Union> (range A))) \<in> borel_measurable (kernel_source K)"
      using measurable_cong by force
  qed
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
        using * by (intro nn_integral_sum, measurable)
      also have "... = (\<Sum>y \<in> g ` space ?M. y * (\<integral>\<^sup>+\<omega>\<^sub>2. (indicator (g -` {y} \<inter> space ?M)(\<omega>\<^sub>1, \<omega>\<^sub>2)) \<partial>kernel_measure K \<omega>\<^sub>1))"
        apply (subst nn_integral_cmult)
        using * by measurable
      also have "... = (\<Sum>y \<in> g ` space ?M. y * I (indicator (g -` {y} \<inter> space ?M)) \<omega>\<^sub>1)"
        unfolding I_def ..
      finally have "I g \<omega>\<^sub>1 = (\<Sum>y \<in> g ` space ?M. y * I (indicator (g -` {y} \<inter> space ?M)) \<omega>\<^sub>1)"
        .
    } note indicator_repr = this
    have "(\<lambda>\<omega>\<^sub>1. (\<Sum>y \<in> g ` space ?M. y * I (indicator (g -` {y} \<inter> space ?M)) \<omega>\<^sub>1)) \<in> borel_measurable (kernel_source K)"
      using * by (measurable, simp add: sigma_G)
    then show "I g \<in> borel_measurable (kernel_source K)"
      by (metis (no_types, lifting) measurable_cong indicator_repr)
  qed
  obtain f' where f': "incseq f'" "f = (SUP i. f' i)"
    "\<And>i. simple_function (kernel_source K \<Otimes>\<^sub>M kernel_target K) (f' i)"
    using borel_measurable_implies_simple_function_sequence[OF f_measurable] by blast
  have "\<And>\<omega>\<^sub>1. \<omega>\<^sub>1 \<in> ?\<Omega>\<^sub>1 \<Longrightarrow> I f \<omega>\<^sub>1 = (SUP i. I (f' i) \<omega>\<^sub>1)"
    unfolding I_def
    apply (subst nn_integral_monotone_convergence_SUP[symmetric])
    using mono_compose[OF f'(1)] apply blast
    apply (metis borel_measurable_simple_function f'(3) measurable_Pair2 measurable_kernel_measure)
    apply (metis SUP_apply f'(2))
    done
  moreover have "(\<lambda>\<omega>\<^sub>1. (SUP i. I (f' i) \<omega>\<^sub>1)) \<in> borel_measurable (kernel_source K)"
    by (measurable, simp add: f'(2, 3))
  ultimately show ?thesis
    using measurable_cong[where g="\<lambda>\<omega>. (\<Squnion>i. I (f' i) \<omega>)"] by blast
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

(* Dirac delta *)
theorem return_kernel[simp]: "transition_kernel M M (return M)"
  apply (rule transition_kernel.intro)
    apply force
  apply (metis measure_space sets_return space_return)
  done

definition return_kernel :: "'a measure \<Rightarrow> 'a hkernel" where
"return_kernel M = hkernel_of M (return M)"

lemma return_kernel_kernel[simp]: "x \<in> space M \<Longrightarrow> kernel (return_kernel M) x = return M x"
  unfolding return_kernel_def apply (auto simp: fun_eq_iff)
  subgoal for A' 
    by (cases "A' \<in> sets M"; simp add: emeasure_notin_sets)
  done

lemma "stochastic_kernel (kernel_of M M (return M))"
  apply (intro stochastic_kernelI)
  apply (simp add: kernel_measure_kernel_of)
  apply (metis measure_of_of_measure prob_space_return sets_return space_return)
  done

text \<open> The emeasure kernel is a kernel that ignores its first argument. \<close>
lemma emeasure_transition_kernel: "transition_kernel M M' (\<lambda>\<omega> A. emeasure M' A)"
  apply unfold_locales
   apply measurable
   apply (simp add: measure_space)
  done

lift_definition emeasure_kernel :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> ('a,'b) kernel" is
"\<lambda> M M'. (M, M', (\<lambda>\<omega> A. if \<omega> \<in> space M then emeasure M' A else 0))"
  unfolding transition_kernel_def apply safe
     apply measurable
    apply (simp add: measure_space)
  apply simp
  apply (meson emeasure_notin_sets)
  done

lemma emeasure_kernel_source[simp]: "kernel_source (emeasure_kernel M M') = M"
  by (transfer, auto)

lemma emeasure_kernel_target[simp]: "kernel_target (emeasure_kernel M M') = M'"
  by (transfer, auto)

lemma emeasure_kernel_notin[simp]: "\<omega> \<notin> space M \<Longrightarrow> (emeasure_kernel M M') \<omega> A' = 0"
  by (transfer, auto)

lemma emeasure_kernel_emeasure[simp]: "\<omega> \<in> space M \<Longrightarrow> (emeasure_kernel M M') \<omega> = emeasure M'"
  by (transfer, auto)

lemma kernel_measure_emeasure_kernel[simp]:
  "\<omega> \<in> space M \<Longrightarrow> kernel_measure (emeasure_kernel M M') \<omega> = M'"
  by (transfer, auto simp: measure_of_of_measure)

lemma emeasure_kernel_sigma_finite:
  "sigma_finite_measure M' \<Longrightarrow> sigma_finite_kernel (emeasure_kernel M M')"
  by (simp add: sigma_finite_kernel_def)

lemma emeasure_kernel_finite: "finite_measure M' \<Longrightarrow> finite_kernel (emeasure_kernel M M')"
  by (metis emeasure_kernel_source finite_kernelI kernel_measure_emeasure_kernel)

lemma emeasure_kernel_stochastic:
  "prob_space M' \<Longrightarrow> stochastic_kernel (emeasure_kernel M M')"
  using stochastic_kernelI by force

lemma emeasure_kernel_substochastic:
  "subprob_space M' \<Longrightarrow> substochastic_kernel (emeasure_kernel M M')"
  using substochastic_kernelI by force

lemma discrete_transition_kernel:
  fixes K :: "'a \<Rightarrow> 'b \<Rightarrow> ennreal"
  assumes "finite \<Omega>\<^sub>2"
  shows "transition_kernel (sigma \<Omega>\<^sub>1 (Pow \<Omega>\<^sub>1)) (sigma \<Omega>\<^sub>2 (Pow \<Omega>\<^sub>2)) (\<lambda>\<omega>. sum (K \<omega>))"
proof (intro transition_kernel.intro; clarsimp)
  have "additive (Pow \<Omega>\<^sub>2) (sum (K \<omega>))" for \<omega>
    unfolding additive_def by (metis PowD assms finite_subset sum.union_disjoint)
  then have "countably_additive (Pow \<Omega>\<^sub>2) (sum (K \<omega>))" for \<omega>
    apply (intro ring_of_sets.countably_additiveI_finite)
    using assms Sigma_Algebra.positive_def ring_of_sets_Pow sum.empty by blast+
  then show "measure_space \<Omega>\<^sub>2 (sigma_sets \<Omega>\<^sub>2 (Pow \<Omega>\<^sub>2)) (sum (K \<omega>))" for \<omega>
    by (simp add: Sigma_Algebra.positive_def measure_space_def sigma_algebra.sigma_sets_eq sigma_algebra_Pow)
  show "(\<lambda>\<omega>. sum (K \<omega>) A') \<in> borel_measurable (sigma \<Omega>\<^sub>1 (Pow \<Omega>\<^sub>1))" for A'
    unfolding measurable_def by auto
qed

end