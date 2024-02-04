theory Kernel_Product
  imports Kernel
begin

text \<open> Klenke theorem 14.25 \<close>

text_raw \<open>\DefineSnippet{kernel_product}{\<close>
definition kernel_product :: "('a, 'b) kernel \<Rightarrow> ('a \<times> 'b, 'c) kernel \<Rightarrow> ('a, 'b \<times> 'c) kernel" (infixr "(\<Otimes>\<^sub>K)" 90) where
"kernel_product K_1 K_2 \<equiv> kernel_of (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
  (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))\<partial>kernel_measure K_1 \<omega>\<^sub>0)"
text_raw \<open>}%EndSnippet\<close>

lemma kernel_product_source[simp]: "kernel_source (K_1 \<Otimes>\<^sub>K K_2) = kernel_source K_1"
  unfolding kernel_product_def by simp

lemma kernel_product_target[simp]: "kernel_target (K_1 \<Otimes>\<^sub>K K_2) = (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
  unfolding kernel_product_def by simp

text_raw \<open>\DefineSnippet{kernel_product_partial}{\<close>
definition kernel_product_partial :: "('a, 'b) kernel \<Rightarrow> ('b, 'c) kernel \<Rightarrow> ('a, 'b \<times> 'c) kernel" (infixr "(\<Otimes>\<^sub>P)" 90) where
"kernel_product_partial K_1 K_2 \<equiv> K_1 \<Otimes>\<^sub>K (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2)
 (\<lambda>\<omega> A\<^sub>2. kernel K_2 (snd \<omega>) A\<^sub>2))"
text_raw \<open>}%EndSnippet\<close>

lemma kernel_product_partial_source[simp]: "kernel_source (K_1 \<Otimes>\<^sub>P K_2) = kernel_source K_1"
  unfolding kernel_product_partial_def by simp

lemma kernel_product_partial_target[simp]: "kernel_target (K_1 \<Otimes>\<^sub>P K_2) = (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
  unfolding kernel_product_partial_def by simp

lemma
  assumes "A \<in> sets (M1 \<Otimes>\<^sub>M M2)"
  shows measurable_pair_fst[measurable]: "\<And>x. x \<in> space M1 \<Longrightarrow> {a. (x,a) \<in> A} \<in> sets M2"
    and measurable_pair_snd[measurable]: "\<And>x. x \<in> space M2 \<Longrightarrow> {a. (a,x) \<in> A} \<in> sets M1"
proof -
  have "A \<in> sigma_sets (space M1 \<times> space M2) {(a \<times> b)| a b . a\<in> sets M1 \<and> b \<in> sets M2}"
    using assms sets_pair_measure by blast
  then show "\<And>x. x \<in> space M1 \<Longrightarrow> {a. (x,a) \<in> A} \<in> sets M2"
            "\<And>x. x \<in> space M2 \<Longrightarrow> {a. (a,x) \<in> A} \<in> sets M1"
  proof induct
    case (Basic a)
    then show "\<And>x. {aa. (x, aa) \<in> a} \<in> sets M2" "\<And>x. {aa. (aa, x) \<in> a} \<in> sets M1"
      by (auto, smt (verit) mem_Collect_eq set_eq_iff sets.sets_Collect(5))
  next
    case Empty
    then show "\<And>x. {a. (x, a) \<in> {}} \<in> sets M2" "\<And>x. {a. (a, x) \<in> {}} \<in> sets M1" by auto
  next
    case (Compl a)
    then have "\<And>x. x \<in> space M1 \<Longrightarrow> space M2 - {aa. (x, aa) \<in> a} \<in> sets M2"
      by auto
    moreover have "\<And>x. x \<in> space M2 \<Longrightarrow> space M1 - {aa. (aa, x) \<in> a} \<in> sets M1"
      using Compl by auto
    ultimately show 
        "\<And>x. x \<in> space M1 \<Longrightarrow> {aa. (x, aa) \<in> space M1 \<times> space M2 - a} \<in> sets M2"
        "\<And>x. x \<in> space M2 \<Longrightarrow> {aa. (aa, x) \<in> space M1 \<times> space M2 - a} \<in> sets M1"
      apply auto
      by (smt (verit, ccfv_SIG) Collect_cong assms(1) mem_Collect_eq set_diff_eq)+
  next
    case (Union a)
    then have "\<And>x. x \<in> space M1 \<Longrightarrow> (\<Union>i. {aa. (x, aa) \<in> a i}) \<in> sets M2"
      by auto
    moreover have "\<And>x. x \<in> space M2 \<Longrightarrow> (\<Union>i. {aa. (aa, x) \<in> a i}) \<in> sets M1"
      using Union by auto
    ultimately show "\<And>x. x \<in> space M1 \<Longrightarrow> {aa. (x, aa) \<in> \<Union> (range a)} \<in> sets M2"
                    "\<And>x. x \<in> space M2 \<Longrightarrow> {aa. (aa, x) \<in> \<Union> (range a)} \<in> sets M1"
      by (auto simp: Collect_ex_eq)
  qed
qed

text \<open> Required for monotone convergence in the below theorem \<close>

text_raw \<open>\DefineSnippet{kernel_snd_measurable}{\<close>
lemma kernel_snd_measurable:
  fixes K :: "('a\<times>'b, 'c) kernel"
  assumes A_sets: "A \<in> sets (M1 \<Otimes>\<^sub>M kernel_target K)"
  and sets_eq: "sets (kernel_source K) = sets (M0 \<Otimes>\<^sub>M M1)"
  and \<omega>\<^sub>0: "\<omega>\<^sub>0 \<in> space M0"
  and finite_kernel: "finite_kernel K"
  shows "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) \<in> borel_measurable M1"
text_raw \<open>}%EndSnippet\<close>
proof -
  define M2 where "M2 \<equiv> kernel_target K"
  let ?G = "{x \<times> y | x y. x \<in> sets M1 \<and> y \<in> sets M2}"
  have sigma_G: "sigma_sets (space (M1 \<Otimes>\<^sub>M M2)) ?G = sets (M1 \<Otimes>\<^sub>M M2)"
    by (metis sets_pair_measure space_pair_measure)
  have "Int_stable ?G"
    using Int_stable_pair_measure_generator by blast
  moreover have "?G \<subseteq> Pow (space (M1 \<Otimes>\<^sub>M M2))"
    by (simp add: pair_measure_closed space_pair_measure)
  moreover have "A \<in> sigma_sets (space (M1 \<Otimes>\<^sub>M M2)) ?G"
    using M2_def A_sets sigma_G by blast
  ultimately show ?thesis
  proof (induct rule: sigma_sets_induct_disjoint)
    case (basic A)
    then obtain x y where xy: "A = x \<times> y" "x \<in> sets M1"  "y \<in> sets M2"
    by blast
    then have "w \<in> x \<Longrightarrow> {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A} = y" for w
      by blast
    moreover have "w \<notin> x \<Longrightarrow> {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A} = {}" for w
      using xy by blast
    moreover have "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) A') \<in> borel_measurable M1" if "A' \<in> sets M2" for A'
      using assms that M2_def by (measurable, auto)
    ultimately show "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) \<in> borel_measurable M1"
      using xy apply auto
      apply measurable
        apply (smt (verit, ccfv_SIG) M2_def empty_Collect_eq mem_Collect_eq sets.empty_sets subsetI subset_antisym)
      using assms(2,3) apply force
      unfolding pred_def by auto
  next
    case empty
    then show ?case by simp
  next
    case (compl A)
    {
      fix w assume w: "w \<in> space M1"
      then have space: "{\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> space (M1 \<Otimes>\<^sub>M M2)} = space M2"
        unfolding space_pair_measure by auto
      from w have "(\<omega>\<^sub>0, w) \<in> space (kernel_source K)"
        by (metis assms(2,3) SigmaI sets_eq_imp_space_eq space_pair_measure)
      then have "finite_measure (kernel_measure K (\<omega>\<^sub>0, w))"
        by (simp add: finite_kernel.finite_measures finite_kernel)
      then have "kernel_measure K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) = 
          kernel_measure K (\<omega>\<^sub>0, w) (space M2) - kernel_measure K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}"
        unfolding M2_def apply (subst kernel_measure_space[THEN sym])+
        apply (rule emeasure_compl)
        using sigma_G compl M2_def w apply force
        by (metis finite_measure.emeasure_finite infinity_ennreal_def)
      then have "K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) = K (\<omega>\<^sub>0, w) (space M2) - K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}"
        using kernel_measure_emeasure by metis
    } note diff = this
    have space_eq: "{\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> space (M1 \<Otimes>\<^sub>M M2)} = space M2" if "w \<in> space M1" for w
      by (simp add: that space_pair_measure)
    have "(\<lambda>w. K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A})) \<in> borel_measurable M1"
      apply (subst measurable_cong[OF diff])
       apply simp
      unfolding M2_def using sets_eq apply measurable
      using \<omega>\<^sub>0 apply simp
       apply auto
      using compl by simp
    then show ?case
      apply (subst measurable_cong[where g="(\<lambda>w. K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}))"])
       apply (smt (verit, best) Collect_cong Diff_iff mem_Collect_eq minus_set_def space_eq)
      apply simp 
      done
  next
    case (union A)
    {
      fix w assume w: "w \<in> space M1"
      then have "(\<omega>\<^sub>0, w) \<in> space (kernel_source K)"
        using \<omega>\<^sub>0 sets_eq_imp_space_eq[OF sets_eq] space_pair_measure by blast
      then have "measure_space (space M2) (sets M2) (kernel K (\<omega>\<^sub>0, w))"
        using kernel.space_source_measure unfolding M2_def by fast
      then have countably_additive: "countably_additive (sets M2) (kernel K (\<omega>\<^sub>0, w))"
        unfolding measure_space_def by blast
      have 1: "range (\<lambda>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i}) \<subseteq> sets M2"
        using union(2) sigma_G w unfolding M2_def by force
      have 2: "disjoint_family (\<lambda>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i})"
        using union(1) unfolding disjoint_family_on_def by auto
      have 3: "(\<Union>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i}) \<in> sets M2"
        using 1 by blast
      have 4: "{\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> \<Union>(range A)} = (\<Union>i. {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i})"
        by blast
      have "kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> \<Union>(range A)} = (\<Sum>i. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A i})"
        using countably_additive 1 2 3 4 unfolding countably_additive_def by presburger
    } note additive = this
    then show "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> \<Union>(range A)}) \<in> borel_measurable M1"
      apply (subst measurable_cong[OF additive])
       apply simp
      using borel_measurable_suminf union by auto
  qed
qed

text \<open> Klenke theorem 14.25 \<close>

text_raw \<open>\DefineSnippet{kernel_product_transition_kernel}{\<close>
theorem kernel_product_transition_kernel:
  fixes K_1 :: "('a, 'b) kernel"
    and K_2 :: "('a\<times>'b, 'c) kernel"
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
    shows "transition_kernel (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
    (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
  (is "transition_kernel ?\<Omega>\<^sub>1 ?\<Omega>\<^sub>2 ?\<kappa>")
text_raw \<open>}%EndSnippet\<close>
proof (intro transition_kernel.intro)
  let ?M0 = "kernel_source K_1"
  and ?M1 = "kernel_target K_1"
  and ?M2 = "kernel_target K_2"

  let ?f = "(\<lambda>A'. \<lambda>(\<omega>\<^sub>1, \<omega>\<^sub>2). indicator A' (snd \<omega>\<^sub>1, \<omega>\<^sub>2))"
  let ?g = "\<lambda>f. (\<lambda> x. \<integral>\<^sup>+\<omega>\<^sub>2. f (x, \<omega>\<^sub>2) \<partial>kernel_measure K_2 x)"

  fix A' assume A': "A' \<in> sets (?M1 \<Otimes>\<^sub>M ?M2)"
  have "?f A' \<in> borel_measurable ((?M0 \<Otimes>\<^sub>M ?M1) \<Otimes>\<^sub>M ?M2)"
    apply measurable
    unfolding pred_def using A' by simp
  then have "(\<lambda> x. \<integral>\<^sup>+\<omega>\<^sub>2. ?f A' (x, \<omega>\<^sub>2) \<partial>kernel_measure K_2 x) \<in> borel_measurable (?M0 \<Otimes>\<^sub>M ?M1)"
    apply measurable
      apply (metis eq measurable_ident_sets sets_pair_measure_cong)
      apply (simp add: finite(2))
      using eq measurable_ident_sets apply blast
    done
  then show "(\<lambda>\<omega>\<^sub>0. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A' (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) \<in> borel_measurable (kernel_source K_1)"
    apply simp
    by (smt (verit, best) kernel_measure_pair_integral_measurable local.finite(1) measurable_cong nn_integral_cong snd_conv)
next
  fix \<omega>\<^sub>0 assume *: "\<omega>\<^sub>0 \<in> space (kernel_source K_1)"
  have "countably_additive (sets ?\<Omega>\<^sub>2) (?\<kappa> \<omega>\<^sub>0)"
  proof (auto simp add: countably_additive_def)
    fix A :: "nat \<Rightarrow> ('b \<times> 'c) set"
    assume range: "range A \<subseteq> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
          and disj: "disjoint_family A"
    have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (\<Union> (range A)) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
        \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. (\<Sum>n. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2)) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      by (simp add: suminf_indicator[OF disj, THEN sym])
    also have "... = \<integral>\<^sup>+ \<omega>\<^sub>1. (\<Sum>n. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      apply (rule nn_integral_cong)
      apply (rule nn_integral_suminf)
      apply measurable
      unfolding pred_def using range apply simp
      done
    also have "... = (\<Sum>i. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A i) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
    proof (rule nn_integral_suminf)
      fix n
      have A_n_measurable [measurable]: "A n \<in> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
        using range by auto
      then have A_n_sigma: "A n \<in> sigma_sets (space (kernel_target K_1) \<times> space (kernel_target K_2))
 {a \<times> b |a b. a \<in> sets (kernel_target K_1) \<and> b \<in> sets (kernel_target K_2)}"
        using sets_pair_measure by blast
      {
        fix \<omega>\<^sub>1 assume \<omega>\<^sub>1: "\<omega>\<^sub>1 \<in> space (kernel_measure K_1 \<omega>\<^sub>0)"
        define A' where "A' = {\<omega>\<^sub>2. (\<omega>\<^sub>1, \<omega>\<^sub>2) \<in> A n}"
        have "(\<lambda>\<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2)) = indicator A'"
          unfolding A'_def indicator_def by auto
        then have "(\<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))
                 = (\<integral>\<^sup>+ \<omega>\<^sub>2. indicator A' \<omega>\<^sub>2 \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))"
          by (simp add: A'_def indicator_def)
        also have "... = emeasure (kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) A'"
          apply (rule nn_integral_indicator)
          unfolding A'_def using A_n_measurable \<omega>\<^sub>1 by auto
        finally have "(\<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) =
                             emeasure (kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) A'"
          .
      } note A = this
      moreover have "(\<lambda>w. kernel K_2 (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A n}) \<in> borel_measurable (kernel_measure K_1 \<omega>\<^sub>0)"
        by (simp add: measurable_kernel_measure kernel_snd_measurable[OF A_n_measurable eq * finite(2)])
      ultimately show "(\<lambda>x. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A n) (x, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, x)) \<in> borel_measurable (kernel_measure K_1 \<omega>\<^sub>0)"
        by (smt (verit, ccfv_SIG) kernel_measure_emeasure measurable_cong)
    qed
    finally show "(\<Sum>i. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (A i) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
         \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator (\<Union> (range A)) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      ..
  qed
  then show "measure_space (space ?\<Omega>\<^sub>2) (sets ?\<Omega>\<^sub>2) (?\<kappa> \<omega>\<^sub>0)"
    unfolding measure_space_def apply auto                                                          
    using sets.sigma_algebra_axioms apply blast
    unfolding positive_def by auto
qed

corollary kernel_prod_apply:
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
      and "\<omega>\<^sub>0 \<in> space (kernel_source K_1)" "A \<in> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
    shows "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 A = (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
  unfolding kernel_product_def
  apply (rule kernel_apply_kernel_of[OF assms(4,5)])
  by (rule kernel_product_transition_kernel[OF assms(1-3)])

lemma kernel_prod_partial_transition_kernel:
  fixes K_1 :: "('a, 'b) kernel"
    and K_2 :: "('b, 'c) kernel"
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_target K_1)"
    shows "transition_kernel (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
    (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
proof -
  have 1: "kernel_measure (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2)
   (\<lambda>\<omega>. kernel K_2 (snd \<omega>))) (\<omega>\<^sub>0, \<omega>\<^sub>1) = kernel_measure K_2 \<omega>\<^sub>1"
    if "\<omega>\<^sub>0 \<in> space (kernel_source K_1)" for \<omega>\<^sub>0 \<omega>\<^sub>1
    apply (simp add: kernel_measure_altdef)
  apply (rule measure_of_eq)
   apply (rule sets.space_closed)
  apply (simp add: sets.sigma_sets_eq)
  apply (cases "\<omega>\<^sub>1 \<in> space (kernel_source K_2)")
   apply (subst kernel_apply_kernel_of)
      apply (auto simp: space_pair_measure)
  unfolding transition_kernel_def
  apply (simp_all add: that)
  apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
  done
  have 2: "(\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
  \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2) (\<lambda>\<omega>. kernel K_2 (snd \<omega>))) (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0"
    for \<omega>\<^sub>0 A
    apply (cases "\<omega>\<^sub>0 \<in> space (kernel_source K_1)")
    apply (rule nn_integral_cong)
     apply (simp add: 1)
    apply (simp add: kernel_measure_notin_space)
    by (metis nn_integral_null_measure null_measure_def)
  show ?thesis
    apply (subst 2)
    using kernel_product_transition_kernel[of K_1 "kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2) (\<lambda>\<omega>. kernel K_2 (snd \<omega>))"]
    apply simp
    using finite eq
    by (smt (verit) 1 SigmaE finite_kernel.finite_measures finite_kernelI sets_pair_measure_cong source_kernel_of space_pair_measure)
qed

corollary kernel_prod_partial_apply:
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_target K_1)"
      and in_space: "\<omega>\<^sub>0 \<in> space (kernel_source K_1)"
      and in_sets: "A \<in> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
    shows "kernel (K_1 \<Otimes>\<^sub>P K_2) \<omega>\<^sub>0 A = (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
proof -
  have 1: "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2)
                 (kernel_target K_2) (\<lambda>\<omega>. kernel K_2 (snd \<omega>))) (\<omega>\<^sub>0, \<omega>\<^sub>1) \<partial>kernel_measure K_1 \<omega>\<^sub>0) =
    \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1 \<partial>kernel_measure K_1 \<omega>\<^sub>0"
      if "\<omega>\<^sub>0 \<in> space (kernel_source K_1)" for \<omega>\<^sub>0 A
    apply (rule nn_integral_cong)
    subgoal for x
      apply (intro arg_cong[where f="\<lambda>M. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (x, \<omega>\<^sub>2) \<partial>M"])
      using that apply (subst kernel_measure_kernel_of)
        apply (simp add: space_pair_measure eq[THEN sets_eq_imp_space_eq])
       apply (intro transition_kernel.intro)
        apply (measurable, assumption)
        apply measurable
       apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
      unfolding kernel_measure_altdef apply simp
      done
    done
  show ?thesis
    unfolding kernel_product_partial_def kernel_product_def
  apply (subst kernel_apply_kernel_of[OF in_space])
    using in_sets apply simp
     apply (subst transition_kernel_cong[where g="\<lambda>\<omega>\<^sub>0 A.\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 \<omega>\<^sub>1 \<partial>kernel_measure K_1 \<omega>\<^sub>0"])
    using 1 apply blast
     apply simp
    using kernel_prod_partial_transition_kernel[OF assms(1-3)] apply blast
    using 1 in_space apply blast
    done
qed

lemma kernel_product_sigma_finite:
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
    shows "sigma_finite_kernel (K_1 \<Otimes>\<^sub>K K_2)"
proof -
  {
    fix \<omega>\<^sub>0 assume \<omega>: "\<omega>\<^sub>0 \<in> space (kernel_source K_1)"
    define A where "A \<equiv> (\<lambda>\<omega>\<^sub>0 (n :: nat). {\<omega>\<^sub>1 \<in> space (kernel_target K_1). kernel K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1) (space (kernel_target K_2)) < n})"
    then have kernel_leq: "x \<in> (A \<omega>\<^sub>0 n) \<Longrightarrow> kernel K_2 (\<omega>\<^sub>0, x) (space (kernel_target K_2)) \<le> n" for x n
      by fastforce
    have A_sets: "A \<omega>\<^sub>0 n \<in> sets (kernel_target K_1)" for n
      unfolding A_def apply measurable
      by (metis \<omega> eq measurable_Pair1' measurable_cong_sets)
    have "countable (range (A \<omega>\<^sub>0))"
      by blast
    have "(kernel K_2 (\<omega>\<^sub>0, x) (space (kernel_target K_2))) \<noteq> \<infinity>" for x
      by (simp add: finite_kernel_finite local.finite(2))
    then have *: "x \<in> space (kernel_target K_1) \<Longrightarrow> \<exists>m \<in> {Suc 0..}. (kernel K_2 (\<omega>\<^sub>0, x) (space (kernel_target K_2))) < of_nat m" for x
      by (metis Suc_leI atLeast_iff gr0I infinity_ennreal_def not_less_zero of_nat_0 top.not_eq_extremum ennreal_Ex_less_of_nat)
    have "(\<Union>n :: nat \<in> {1..}. A \<omega>\<^sub>0 n) = space (kernel_target K_1)"
      unfolding A_def by (auto simp add: set_eq_iff * )
    have sigma_finite: "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) < \<infinity>" for n :: nat
    proof -
      have "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) = 
 (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))\<partial>kernel_measure K_1 \<omega>\<^sub>0)"
        apply (rule kernel_prod_apply[OF assms \<omega>])
        using A_sets sets_pair_measure by auto
      also have L: "... = \<integral>\<^sup>+ \<omega>\<^sub>1. indicator (A \<omega>\<^sub>0 n) \<omega>\<^sub>1 * emeasure (kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) (space (kernel_target K_2))
       \<partial>kernel_measure K_1 \<omega>\<^sub>0"
        apply (auto simp: indicator_times A_def)
        apply (subst(2) nn_integral_eq_simple_integral)
        by auto
      also have "... \<le> \<integral>\<^sup>+ \<omega>\<^sub>1. (of_nat n) * indicator (A \<omega>\<^sub>0 n) \<omega>\<^sub>1 \<partial>kernel_measure K_1 \<omega>\<^sub>0"
        apply (rule nn_integral_mono)
        unfolding A_def
        by (metis (no_types, lifting) indicator_simps(1) indicator_simps(2) kernel_measure_emeasure
            linorder_not_less mem_Collect_eq mult.commute mult.right_neutral mult_zero_right order_less_imp_le)
      also have "... \<le> n * kernel K_1 \<omega>\<^sub>0 (A \<omega>\<^sub>0 n)"
        apply (subst nn_integral_cmult_indicator)
        using A_sets kernel_measure_sets apply fast
        apply (subst kernel_measure_emeasure) ..
      also have "... < \<infinity>"
      by (metis finite_kernel_finite finite(1) ennreal_less_top ennreal_mult_eq_top_iff 
              ennreal_of_nat_eq_real_of_nat infinity_ennreal_def top.not_eq_extremum)
    finally show "kernel (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0 (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)) < \<infinity>"
      by simp
  qed
    let ?A = "range (\<lambda>n. (A \<omega>\<^sub>0 n \<times> space (kernel_target K_2)))"
    have "countable ?A \<and>
             ?A \<subseteq> sets (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2) \<and>
             \<Union> ?A = space (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2) \<and>
             (\<forall>a\<in>?A. emeasure (kernel_measure (K_1 \<Otimes>\<^sub>K K_2) \<omega>\<^sub>0) a \<noteq> \<top>)"
      apply auto
      prefer 5 
          apply (metis infinity_ennreal_def top.not_eq_extremum sigma_finite)
      unfolding A_def using assms \<omega> apply measurable
        apply (simp add: space_pair_measure)
      using "*" space_pair_measure apply fastforce
      by (simp add: space_pair_measure)
  }
  then show "sigma_finite_kernel (K_1 \<Otimes>\<^sub>K K_2)"
    apply (intro sigma_finite_kernel.intro sigma_finite_measure.intro)
    by (metis (mono_tags, lifting) infinity_ennreal_def kernel_measure_sets kernel_measure_space kernel_product_source kernel_product_target)
qed

lemma kernel_product_stochastic:    
  assumes stochastic: "stochastic_kernel K_1" "stochastic_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
    shows "stochastic_kernel (K_1 \<Otimes>\<^sub>K K_2)"
proof (rule stochastic_kernelI)
  fix \<omega> assume *: "\<omega> \<in> space (kernel_source (K_1 \<Otimes>\<^sub>K K_2))"
  have "finite_kernel K_1" "finite_kernel K_2"
    using assms stochastic_kernel.axioms(1) by blast+
  then have "(K_1 \<Otimes>\<^sub>K K_2) \<omega> (space (kernel_target (K_1 \<Otimes>\<^sub>K K_2))) = \<integral>\<^sup>+ \<omega>\<^sub>1. emeasure (kernel_measure K_2 (\<omega>, \<omega>\<^sub>1)) (space (kernel_target K_2)) \<partial>kernel_measure K_1 \<omega>"
    apply (subst kernel_prod_apply)
    using * apply (simp_all add: assms)
    apply (simp add: space_pair_measure indicator_times)
    apply (subst(2) nn_integral_eq_simple_integral)
     apply auto
    apply (rule nn_integral_cong)
    by simp
  also have "... = \<integral>\<^sup>+ \<omega>\<^sub>1. 1 \<partial>kernel_measure K_1 \<omega>"
    apply (rule nn_integral_cong)
    by (metis (full_types) "*" SigmaI eq kernel_measure_space kernel_product_source prob_space.emeasure_space_1 sets_eq_imp_space_eq space_pair_measure stochastic(2) stochastic_kernel.probability_measures)
  also have "... = 1"
    using stochastic(1) * prob_space.emeasure_space_1 stochastic_kernel.probability_measures by fastforce
  finally show "prob_space (kernel_measure (K_1 \<Otimes>\<^sub>K K_2) \<omega>)"
    by (auto intro: prob_spaceI)
qed

(* CARBON COPY OF THE ABOVE *)
lemma kernel_product_substochastic:    
  assumes substochastic: "substochastic_kernel K_1" "substochastic_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
      and nonempty: "space (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2) \<noteq> {}" 
        (* Could remove nonempty assumption with changes to substochastic locale *)
    shows "substochastic_kernel (K_1 \<Otimes>\<^sub>K K_2)"
proof (rule substochastic_kernelI)
  fix \<omega> assume *: "\<omega> \<in> space (kernel_source (K_1 \<Otimes>\<^sub>K K_2))"
  have "finite_kernel K_1" "finite_kernel K_2"
    using assms substochastic_kernel.axioms(1) by blast+
  then have "(K_1 \<Otimes>\<^sub>K K_2) \<omega> (space (kernel_target (K_1 \<Otimes>\<^sub>K K_2))) \<le>
   \<integral>\<^sup>+ \<omega>\<^sub>1. emeasure (kernel_measure K_2 (\<omega>, \<omega>\<^sub>1)) (space (kernel_target K_2)) \<partial>kernel_measure K_1 \<omega>"
    apply (subst kernel_prod_apply)
    using * apply (simp_all add: assms)
    apply (simp add: space_pair_measure indicator_times)
    apply (subst(2) nn_integral_eq_simple_integral)
     apply auto
    apply (rule nn_integral_mono)
    by simp
  also have "... \<le>  \<integral>\<^sup>+ \<omega>\<^sub>1. 1 \<partial>kernel_measure K_1 \<omega>"
    apply (rule nn_integral_mono)
    by (metis substochastic(2) kernel_measure_emeasure kernel_not_space_zero
        linordered_nonzero_semiring_class.zero_le_one subprob_space.subprob_emeasure_le_1 
        substochastic_kernel.subprob_measures)
  also have "... \<le> 1"
    apply simp
    using substochastic
    by (simp add: substochastic_kernel.kernel_leq_1)
  finally show "subprob_space (kernel_measure (K_1 \<Otimes>\<^sub>K K_2) \<omega>)"
    by (auto intro: subprob_spaceI simp: nonempty)
qed

lemma kernel_product_partial_stochastic:
  assumes "stochastic_kernel K\<^sub>1" "stochastic_kernel K\<^sub>2"
    and "sets (kernel_target K\<^sub>1) = sets (kernel_source K\<^sub>2)"
  shows "stochastic_kernel (K\<^sub>1 \<Otimes>\<^sub>P K\<^sub>2)"
  unfolding kernel_product_partial_def
  apply (intro kernel_product_stochastic)
    apply (fact assms(1))
   apply (intro stochastic_kernelI)
  sorry

section \<open> Kernel semidirect product \<close>

lemma arg_cong3: "\<lbrakk>a = d; b = e; c = f\<rbrakk> \<Longrightarrow> g a b c = g d e f"
  by simp

lemma semidirect_product_unique:
  assumes space: "x \<in> space M" "y \<in> space M"
    and finite: "finite_measure M" "finite_kernel K"
    and sets: "sets M = sets (kernel_source K)"
  shows "kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) x = kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) y"
  unfolding kernel_measure_altdef
  apply (rule arg_cong3[where g=measure_of])
    apply simp_all
  apply (simp add: fun_eq_iff)
  apply (intro allI)
  subgoal for A'
    apply (cases "A' \<in> sets (M \<Otimes>\<^sub>M kernel_target K)")
     apply (subst kernel_prod_partial_apply)
    using finite defer
    using finite apply blast
    using sets apply simp
    using space apply simp
    using sets apply simp
     apply (subst kernel_prod_partial_apply)
    using finite defer
    using finite apply blast
    using sets apply simp
    using space apply simp
    using sets apply simp
    using assms apply simp
      apply simp
    using emeasure_kernel_finite local.finite(1) apply blast+
    done
  done

text_raw \<open>\DefineSnippet{kernel_semidirect_product}{\<close>
definition kernel_semidirect_product :: "'a measure \<Rightarrow> ('a, 'b) kernel \<Rightarrow> ('a \<times> 'b) measure" (infixr "(\<Otimes>\<^sub>S)" 70)
  where "M \<Otimes>\<^sub>S K = kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) (SOME \<omega>. \<omega> \<in> space (kernel_source K))"
text_raw \<open>}%EndSnippet\<close>

lemma space_kernel_semidirect_product[simp]: "space (M \<Otimes>\<^sub>S K) = (space M \<times> space (kernel_target K))"
  unfolding kernel_semidirect_product_def by (simp add: space_pair_measure)

lemma sets_kernel_semidirect_product[measurable]: "sets (M \<Otimes>\<^sub>S K) = sets (M \<Otimes>\<^sub>M (kernel_target K))"
  unfolding kernel_semidirect_product_def 
  by (simp add: kernel_product_partial_def)

lemma kernel_semidirect_product_measurable[measurable]: 
  "f \<in> M \<Otimes>\<^sub>S K \<rightarrow>\<^sub>M M' \<longleftrightarrow> f \<in> M \<Otimes>\<^sub>M (kernel_target K) \<rightarrow>\<^sub>M M'"
  using measurable_cong_sets[OF sets_kernel_semidirect_product] by blast

locale finite_measure_kernel = K?: finite_kernel K + M?: finite_measure M
  for K :: "('a, 'b) kernel" and M :: "'a measure" +
  assumes sets_eq: "sets (kernel_source K) = sets M"
      and nonempty: "space M \<noteq> {}"
begin

lemma space_eq: "space (kernel_source K) = space M"
  by (fact sets_eq_imp_space_eq[OF sets_eq])

text_raw \<open>\DefineSnippet{emeasure_semidirect_product}{\<close>
lemma emeasure_semidirect_product:
  assumes "A \<in> sets (M \<Otimes>\<^sub>S K)"
  shows "emeasure (M \<Otimes>\<^sub>S K) A = \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M"
text_raw \<open>}%EndSnippet\<close>
  unfolding kernel_semidirect_product_def 
  apply (subst kernel_measure_emeasure)
  apply (subst kernel_prod_partial_apply)
  using emeasure_kernel_finite finite_measure_axioms apply blast
  using finite_kernel_axioms apply blast
     apply (simp add: sets_eq)
    apply (simp add: nonempty some_in_eq space_eq)
  using assms apply (simp add: sets_kernel_semidirect_product)
  apply (simp add: nonempty some_in_eq space_eq)
  done

lemma emeasure_times_semidirect_product: 
  assumes "A \<in> sets M" "B \<in> sets (kernel_target K)"
  shows "emeasure (M \<Otimes>\<^sub>S K) (A \<times> B) = \<integral>\<^sup>+\<omega>\<^sub>1 \<in> A. K \<omega>\<^sub>1 B \<partial>M"
  apply (subst emeasure_semidirect_product)
  using assms sets_kernel_semidirect_product apply blast
  apply (simp add: indicator_times assms(2) mult.commute nn_integral_cmult_indicator)
  done

text_raw \<open>\DefineSnippet{kernel_Fubini}{\<close>
lemma kernel_Fubini:
  assumes f[measurable]: "f \<in> borel_measurable (M \<Otimes>\<^sub>M (kernel_target K))"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. f (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M)"
text_raw \<open>}%EndSnippet\<close>
using f proof induct
  case (cong f g)
  have "integral\<^sup>N (M \<Otimes>\<^sub>S K) f = integral\<^sup>N (M \<Otimes>\<^sub>S K) g"
    by (intro nn_integral_cong, simp add: space_pair_measure cong(3))
  moreover have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. f (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
                 (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. g (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (rule nn_integral_cong)+
    using cong(3) space_pair_measure by fastforce
  ultimately show ?case
    using cong(4) by argo
next
  case (set A)
  then show ?case
    by (simp add: emeasure_semidirect_product sets_kernel_semidirect_product)
next
  case (mult u v)
  have L: "(\<integral>\<^sup>+ \<omega>. v * u \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = v * (\<integral>\<^sup>+ \<omega>. u \<omega> \<partial>(M \<Otimes>\<^sub>S K))"
    using nn_integral_cmult kernel_semidirect_product_measurable mult.hyps(2) by blast
  have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v * u (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
         \<integral>\<^sup>+ \<omega>\<^sub>1. v * (\<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M"
    apply (rule nn_integral_cong)
    apply (intro nn_integral_cmult)
     apply (metis mult.hyps(2) measurable_Pair2 measurable_kernel_measure)
    done
  also have "... = v * (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (rule nn_integral_cmult)
    using mult.hyps(2) sets_eq finite_kernel_axioms by measurable
  finally show ?case
    using L mult.hyps(4) by argo
next
  case (add u v)
  have L: "(\<integral>\<^sup>+ \<omega>. v \<omega> + u \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = (\<integral>\<^sup>+ \<omega>. v \<omega> \<partial>(M \<Otimes>\<^sub>S K)) + (\<integral>\<^sup>+ \<omega>. u \<omega> \<partial>(M \<Otimes>\<^sub>S K))"
    using nn_integral_add kernel_semidirect_product_measurable add.hyps(1,4) by blast
  have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v (\<omega>\<^sub>1, \<omega>\<^sub>2) + u (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
   \<integral>\<^sup>+ \<omega>\<^sub>1. (\<integral>\<^sup>+ \<omega>\<^sub>2. v (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) + (\<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M"
    apply (rule nn_integral_cong)
    apply (intro nn_integral_add)
     apply (metis add.hyps(4) measurable_Pair2 measurable_kernel_measure)
     apply (metis add.hyps(1) measurable_Pair2 measurable_kernel_measure)
    done
  also have "... = (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) 
                 + (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (rule nn_integral_add)
    using add.hyps(1,4) sets_eq finite_kernel_axioms by measurable
  finally show ?case
    using L add.hyps(3,7) by argo
  next
  case (seq U)
  then have 1: "\<And>i. U i \<in> borel_measurable (M \<Otimes>\<^sub>S K)"
    using kernel_semidirect_product_measurable by blast
  have "integral\<^sup>N (M \<Otimes>\<^sub>S K) (\<Squnion> range U) = \<integral>\<^sup>+ x. (\<Squnion>i. U i x) \<partial>(M \<Otimes>\<^sub>S K)"
    by (intro nn_integral_cong SUP_apply)
  then have L: "integral\<^sup>N (M \<Otimes>\<^sub>S K) (\<Squnion> range U) = (\<Squnion>i. integral\<^sup>N (M \<Otimes>\<^sub>S K) (U i))"
    by (simp add: nn_integral_monotone_convergence_SUP[OF seq(4) 1])
  have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. (\<Squnion> range U) (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) =
         \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. (\<Squnion>i. U i (\<omega>\<^sub>1, \<omega>\<^sub>2)) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M"
    by (subst SUP_apply, argo)
  also have "... = \<integral>\<^sup>+ \<omega>\<^sub>1. (\<Squnion>i. \<integral>\<^sup>+ \<omega>\<^sub>2. U i (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M"
    apply (rule nn_integral_cong)
    apply (intro nn_integral_monotone_convergence_SUP)
    using seq(4) mono_compose apply blast
    apply (metis measurable_Pair2 measurable_kernel_measure seq.hyps(1))
    done
  also have "... = (\<Squnion>i. \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. U i (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
    apply (intro nn_integral_monotone_convergence_SUP)
    using seq(4) apply (simp add: incseq_def le_fun_def nn_integral_mono)
    apply measurable
    using seq.hyps(1) sets_eq finite_kernel_axioms apply auto
    done
  finally show ?case
    using L seq(3) by presburger
qed

end

section \<open> Finite product kernel\<close>

text \<open> Given a finite collection of kernels K \<in> I ` {0..n} -> kernel, we define the finite product
  kernel PiK n I K as the iterated integral over each kernel in the collection in order. \<close>

text_raw \<open>\DefineSnippet{PiK}{\<close>
primrec PiK :: "nat \<Rightarrow> (nat \<Rightarrow> 'i) \<Rightarrow> ('i \<Rightarrow> ('a, 'a) kernel) \<Rightarrow> ('a, ('i \<Rightarrow> 'a)) kernel" where
"PiK 0 I K = kernel_of (kernel_source (K (I 0))) (PiM {I 0} (\<lambda>n. kernel_target (K n)))
   (\<lambda> \<omega> A'. (K (I 0)) \<omega> ((\<lambda>x.(\<lambda>n\<in>{I 0}. x)) -` A' \<inter> space (kernel_target (K (I 0)))))" |
"PiK (Suc n) I K = kernel_of (kernel_source (K (I 0))) (PiM (I ` {0..Suc n}) (\<lambda>i. kernel_target (K i)))
  (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f (I (Suc n):=\<omega>)) \<partial>kernel_measure (K (I (Suc n))) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>)"
text_raw \<open>}%EndSnippet\<close>

lemma PiK_source[simp]: "kernel_source (PiK n I K) = kernel_source (K (I 0))"
  by (cases n; simp)

lemma PiK_target[simp]: "kernel_target (PiK n I K) = PiM (I ` {0..n}) (\<lambda>i. kernel_target (K i))"
  by (cases n; simp)

lemma transition_kernel_PiK_0:
  fixes K :: "'i \<Rightarrow> ('a,'a) kernel" and I :: "nat \<Rightarrow> 'i"
  shows "transition_kernel (kernel_source (K (I 0))) (PiM {I 0} (\<lambda>i. kernel_target (K i)))
    (\<lambda> \<omega> A'. (K (I 0)) \<omega> (((\<lambda>x.(\<lambda>n\<in>{I 0}. x)) -` A') \<inter> space (kernel_target (K (I 0)))))"
proof (intro transition_kernel.intro, goal_cases)
  case (1 A')
  then show ?case
    apply measurable
    by (metis (no_types, lifting) 1 sets_PiM_cong singletonD)
next
  case (2 \<omega>)
  then have "countably_additive (sets (kernel_target (K (I 0)))) (K (I 0) \<omega>)"
    by (rule kernel.countably_additive)
  then have *:
    "\<And>A. \<lbrakk>range A \<subseteq> (sets (kernel_target (K (I 0)))); 
           disjoint_family A;
           (\<Union>i. A i) \<in> (sets (kernel_target (K (I 0))))\<rbrakk> \<Longrightarrow>
          (\<Sum>i. (K (I 0) \<omega>) (A i)) = (K (I 0) \<omega>) (\<Union>i. A i)"
    unfolding countably_additive_def by blast
  have "countably_additive (sets (Pi\<^sub>M {I 0} (\<lambda>n. kernel_target (K n))))
     (\<lambda>A'. kernel (K (I 0)) \<omega> ((\<lambda>x. \<lambda>n\<in>{I 0}. x) -` A' \<inter> space (kernel_target (K (I 0)))))"
  proof (intro countably_additiveI)
    fix A :: "nat \<Rightarrow> ('i \<Rightarrow> 'a) set"
    assume A: "range A \<subseteq> sets (Pi\<^sub>M {I 0} (\<lambda>n. kernel_target (K n)))"
         "disjoint_family A"
         "\<Union> (range A) \<in> sets (Pi\<^sub>M {I 0} (\<lambda>n. kernel_target (K n)))"
    have range: "range (\<lambda>i. (\<lambda>x. \<lambda>n\<in>{I 0}. x) -` A i \<inter> space (kernel_target (K (I 0)))) \<subseteq> sets (kernel_target (K (I 0)))"
      apply (intro subsetI)
      apply (erule rangeE)
      apply auto
      apply measurable
      by (smt (verit, ccfv_threshold) A(1) range_subsetD sets_PiM_cong singletonD)
    moreover have "disjoint_family (\<lambda>i. (\<lambda>x. \<lambda>n\<in>{I 0}. x) -` A i \<inter> space (kernel_target (K (I 0))))"
      using A(2) unfolding disjoint_family_on_def by auto
    moreover have "(\<Union>i. (\<lambda>x. \<lambda>n\<in>{I 0}. x) -` A i \<inter> space (kernel_target (K (I 0)))) \<in> sets (kernel_target (K (I 0)))"
      using range by blast
    ultimately have "(\<Sum>i. kernel (K (I 0)) \<omega> ((\<lambda>x. \<lambda>n\<in>{I 0}. x) -` A i \<inter> space (kernel_target (K (I 0))))) = kernel (K (I 0)) \<omega> (\<Union> (range (\<lambda>n. ((\<lambda>x. \<lambda>n\<in>{I 0}. x) -` (A n) \<inter> space (kernel_target (K (I 0)))))))"
      by (rule *)
    also have "... = kernel (K (I 0)) \<omega> ((\<lambda>x. \<lambda>n\<in>{I 0}. x) -` \<Union> (range A) \<inter> space (kernel_target (K (I 0))))"
      by (simp add: vimage_Union)
    finally show "(\<Sum>i. kernel (K (I 0)) \<omega> ((\<lambda>x. \<lambda>n\<in>{I 0}. x) -` A i \<inter> space (kernel_target (K (I 0))))) = kernel (K (I 0)) \<omega> ((\<lambda>x. \<lambda>n\<in>{I 0}. x) -` \<Union> (range A) \<inter> space (kernel_target (K (I 0))))"
      .
  qed
  then show ?case
    unfolding measure_space_def positive_def
    by (smt (verit, del_insts) kernel_empty sets.Int_space_eq2 sets.empty_sets 
        sets.sigma_algebra_axioms sets_PiM_cong singletonD vimage_empty)
qed

lemma transition_kernel_PiK_Suc:
  fixes K :: "'i \<Rightarrow> ('a, 'a) kernel"
  assumes finite: "finite_kernel (PiK n I K)" "finite_kernel (K (I (Suc n)))"
      and source_eq_target: "kernel_target (K (I n)) = kernel_source (K (I (Suc n)))"
  shows "transition_kernel (kernel_source (K (I 0))) (kernel_target (PiK (Suc n) I K))
  (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f (I (Suc n):=\<omega>)) \<partial>kernel_measure (K (I (Suc n))) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>)" (is "transition_kernel ?M ?N' ?\<kappa>")
proof -
  let ?K = "\<lambda>n. K (I n)"
  have eq: "(kernel_of (kernel_target (PiK n I K)) (kernel_target (?K (Suc n)))
    (\<lambda>\<omega>. ?K (Suc n) (\<omega> (I n)))) \<omega>\<^sub>f A' = (?K (Suc n)) (\<omega>\<^sub>f (I n)) A'"
    if "\<omega>\<^sub>f \<in> space (kernel_target (PiK n I K))" for \<omega>\<^sub>f A'
    apply (cases "A' \<in> sets (kernel_target (?K (Suc n)))")
    apply (subst kernel_apply_kernel_of)
       using that apply (auto simp: that)
    apply (intro transition_kernel.intro)
     apply measurable
         apply blast
       apply (metis atLeast0AtMost atMost_iff dual_order.eq_iff image_eqI measurable_component_singleton source_eq_target)
    apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
    done
  have 1: "kernel_measure (kernel_of (kernel_target (PiK n I K)) (kernel_target (?K (Suc n)))
    (\<lambda>\<omega>. ?K (Suc n) (\<omega> (I n)))) \<omega>\<^sub>f = kernel_measure (?K (Suc n)) (\<omega>\<^sub>f (I n))"
    if "\<omega>\<^sub>f \<in> space (kernel_target (PiK n I K))" for \<omega>\<^sub>f
    apply (simp add: kernel_measure_altdef)
    apply (rule measure_of_eq)
     apply (rule sets.space_closed)
    using that apply (simp add: sets.sigma_sets_eq)
   apply (subst kernel_apply_kernel_of)
       apply (auto simp: space_PiM)
    apply (intro transition_kernel.intro)
     apply measurable
      apply blast
       apply (metis atLeast0AtMost atMost_iff dual_order.eq_iff image_eqI measurable_component_singleton source_eq_target)
    apply (metis kernel_measure_emeasure kernel_measure_sets kernel_measure_space measure_space)
    done
  have 2: "(\<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (?K (Suc n)) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>) = (\<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (kernel_of (kernel_target (PiK n I K)) (kernel_target (?K (Suc n)))
    (\<lambda>\<omega>. ?K (Suc n) (\<omega> (I n)))) \<omega>\<^sub>f) \<partial>kernel_measure (PiK n I K) \<omega>)" for \<omega> A'
    apply (cases "\<omega> \<in> space (kernel_source (K (I 0)))")
     apply (rule nn_integral_cong)
    using 1 apply force
    by (metis (mono_tags, lifting) "1" kernel_measure_space nn_integral_cong)
  have 3: "kernel_target (?K (Suc n)) = kernel_target (kernel_of (kernel_target (PiK n I K)) (kernel_target (?K (Suc n))) (\<lambda>\<omega>. kernel (?K (Suc n)) (\<omega> (I n))))"
    by simp
  have "transition_kernel (kernel_source (PiK n I K))
  (kernel_target (PiK n I K) \<Otimes>\<^sub>M (kernel_target (?K (Suc n))))
  (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (?K (Suc n)) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>)"
    apply (subst 2)
    apply (subst 3)
    apply (rule kernel_prod_partial_transition_kernel[of "PiK n I K" "kernel_of (kernel_target (PiK n I K)) (kernel_target (?K (Suc n)))
    (\<lambda>\<omega>. ?K (Suc n) (\<omega> (I n)))"])
    using finite apply simp_all
    apply (intro finite_kernelI finite_measureI)
    apply auto
    by (smt (verit, best) "1" PiK_target PiM_cong finite_kernel_finite kernel_measure_emeasure)
  then have "transition_kernel (kernel_source (PiK n I K)) (kernel_target (PiK (Suc n) I K))
    (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator ((\<lambda>(f,y). f(I (Suc n):=y)) -` A' \<inter> space (kernel_target (PiK n I K) \<Otimes>\<^sub>M (kernel_target (?K (Suc n))))) (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (?K (Suc n)) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>)"
    apply (rule transition_kernel.transition_kernel_distr)
    apply simp
    apply (subst atLeast0_atMost_Suc)
    apply measurable
    by fastforce
  then have "transition_kernel (kernel_source (PiK n I K)) (kernel_target (PiK (Suc n) I K))
    (\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f (I (Suc n) := \<omega>)) \<partial>kernel_measure (?K (Suc n)) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>)"
    apply (subst transition_kernel_cong[where g="(\<lambda>\<omega> A'. \<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator ((\<lambda>(f,y). f(I (Suc n):=y)) -` A' \<inter> space (kernel_target (PiK n I K) \<Otimes>\<^sub>M (kernel_target (?K (Suc n))))) (\<omega>\<^sub>f, \<omega>) \<partial>kernel_measure (?K (Suc n)) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>)"])
     apply (rule nn_integral_cong)
     apply (rule nn_integral_cong)
     apply (smt (verit, best) Int_iff case_prod_conv indicator_simps(1) indicator_simps(2) kernel_measure_space mem_Sigma_iff space_pair_measure vimage_eq)
    by blast
  then show ?thesis by simp
qed

lemma PiK_apply_0:
  assumes "\<omega> \<in> space (kernel_source (K (I 0)))" "A' \<in> sets (PiM {I 0} (\<lambda>n. kernel_target (K n)))"
  shows "PiK 0 I K \<omega> A' = (K (I 0)) \<omega> ((\<lambda>x.(\<lambda>n\<in>{I 0}. x)) -` A' \<inter> space (kernel_target (K (I 0))))"
  apply simp
  apply (subst kernel_apply_kernel_of)
  using assms apply simp_all
  using transition_kernel_PiK_0[of K I]
  by (smt (verit, best) PiM_cong singletonD transition_kernel_PiK_0 transition_kernel_cong vimage_inter_cong)

lemma PiK_apply_Suc:
  assumes "finite_kernel (PiK n I K)" "finite_kernel (K (I (Suc n)))"
    "kernel_target (K (I n)) = kernel_source (K (I (Suc n)))"
    "\<omega> \<in> space (kernel_source (K (I 0)))" "A' \<in> sets (PiM (I ` {0..Suc n}) (\<lambda>n. kernel_target (K n)))"
  shows "PiK (Suc n) I K \<omega> A' = (\<integral>\<^sup>+\<omega>\<^sub>f. (\<integral>\<^sup>+\<omega>. indicator A' (\<omega>\<^sub>f (I(Suc n):=\<omega>)) \<partial>kernel_measure (K (I (Suc n))) (\<omega>\<^sub>f (I n)))
                \<partial>kernel_measure (PiK n I K) \<omega>)"
  using assms apply (simp add: transition_kernel_PiK_Suc)
  using transition_kernel_PiK_Suc[OF assms(1-3)] by auto

locale stochastic_kernel_family =
  fixes K :: "'i \<Rightarrow> ('a, 'a) kernel"
  and I :: "nat \<Rightarrow> 'i"
  and n :: nat
assumes stochastic_kernels: "\<And>k. k \<le> n \<Longrightarrow> stochastic_kernel (K (I k))"
  and consistent_sets: "\<And>k. k < n \<Longrightarrow> kernel_target (K (I k)) = kernel_source (K (I (Suc k)))"
begin

lemma PiK_stochastic:
  shows "stochastic_kernel (PiK n I K)"
  using stochastic_kernels consistent_sets
proof (induct n)
  case 0
  have "(\<lambda>x. \<lambda>n\<in>{I 0}. x) -` space (Pi\<^sub>M {I 0} (\<lambda>n. kernel_target (K n))) \<subseteq> space (kernel_target (K (I 0)))"
    apply (subst space_PiM)
    by force
  then show ?case
    apply (intro stochastic_kernelI prob_spaceI)
    apply (subst kernel_measure_emeasure)
    apply (subst PiK_apply_0)
      apply (metis PiK_source)
    apply auto
    by (smt (verit, ccfv_SIG) "0" Int_absorb2 less_eq_nat.simps(1) restrict_PiE_iff singletonD 
        space_PiM stochastic_kernel.kernel_space_eq_1 subset_antisym subset_vimage_iff)
next
  case (Suc n)
  show ?case
    apply (intro stochastic_kernelI prob_spaceI)
    apply (subst kernel_measure_emeasure)
    apply (subst PiK_apply_Suc)
    using Suc stochastic_kernel_def apply auto[1]
        apply (simp add: Suc.prems stochastic_kernel.axioms(1))
    using Suc.prems(2) apply blast
      apply simp
     apply simp
    apply (simp add: space_PiM)
    apply (subst nn_integral_cong[where v="(\<lambda>_. 1)"])
     apply auto
     apply (subst nn_integral_cong[where v="(\<lambda>_.1)"])
     apply auto
    unfolding indicator_def apply (auto simp: space_PiM)
    apply (metis PiE_iff atLeast0AtMost atMost_iff image_eqI le_SucE)
    using PiE_arb apply fastforce
    apply (simp add: PiE_iff Suc.prems stochastic_kernel.kernel_space_eq_1)
    by (metis Suc PiK_source PiK_target le_SucI less_SucI space_PiM stochastic_kernel.kernel_space_eq_1)
qed
end

locale stochastic_family_measure = K?: stochastic_kernel_family K + M?: prob_space M
  for K :: "'i \<Rightarrow> ('a, 'a) kernel" and M :: "'a measure" +
  assumes sets_eq_measure: "sets (kernel_source (K (I 0))) = sets M"
      and nonempty: "space M \<noteq> {}"

sublocale stochastic_family_measure \<subseteq> finite_measure_kernel "PiK n I K"
  apply (intro finite_measure_kernel.intro)
    apply (rule stochastic_kernel.axioms(1))
    apply (rule PiK_stochastic)
   apply simp
  unfolding finite_measure_kernel_axioms_def using sets_eq_measure nonempty by simp

context stochastic_family_measure begin

definition PiK_semidirect_product where
"PiK_semidirect_product i \<equiv> distr (M \<Otimes>\<^sub>S PiK n I K) (PiM (insert i (I ` {0..n})) ((\<lambda>i. kernel_target (K i))(i := M)))
   ((\<lambda>(x, y). y(i := x)))"

lemma measurable_insert_PiK [measurable]:
  assumes "i \<notin> I ` {0..n}"
  shows "(\<lambda>(x, y). y(i := x)) \<in> (M \<Otimes>\<^sub>S PiK n I K) \<rightarrow>\<^sub>M
   (PiM (insert i (I ` {0..n})) ((\<lambda>i. kernel_target (K i))(i := M)))"
  using sets_kernel_semidirect_product apply measurable
   apply simp
   apply (subst(2) PiM_cong[where J="I`{0..n}" and N= "\<lambda>k. kernel_target (K k)"])
     apply blast
  using assms apply auto[1]
  apply (fact measurable_id)
   apply (simp add: kernel_semidirect_product_measurable)
  done

lemma PiK_semidirect_product_space [simp]:
  "space (PiK_semidirect_product i) = 
   space (PiM (insert i (I ` {0..n})) ((\<lambda>i. kernel_target (K i))(i := M)))"
  unfolding PiK_semidirect_product_def by simp

lemma PiK_semidirect_product_sets [simp]:
  "sets (PiK_semidirect_product i) = 
   sets (PiM (insert i (I ` {0..n})) ((\<lambda>i. kernel_target (K i))(i := M)))"
  unfolding PiK_semidirect_product_def by simp

lemma PiK_semidirect_product_emeasure:
  assumes [simp]: "A \<in> sets (PiK_semidirect_product i)" "i \<notin> I ` {0..n}"
  shows "emeasure (PiK_semidirect_product i) A 
    = \<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. indicator A (\<omega>\<^sub>2(i:=\<omega>\<^sub>1)) \<partial>kernel_measure (PiK n I K) \<omega>\<^sub>1 \<partial>M"
  unfolding PiK_semidirect_product_def
  apply (subst emeasure_distr)
    apply simp
  using assms(1) apply simp
  apply (subst emeasure_semidirect_product)
  using measurable_insert_PiK[OF assms(2)] apply measurable
  using assms(1) PiK_semidirect_product_sets apply blast
  apply (rule nn_integral_cong)
  apply (rule nn_integral_cong)
  using assms apply simp
  by (smt (verit) case_prod_conv indicator_inter_arith indicator_simps(1) indicator_vimage 
      kernel_measure_space mem_Sigma_iff mult.right_neutral sets_eq_imp_space_eq
      sets_kernel_semidirect_product space_pair_measure)
end
text \<open> Klenke theorem 14.31 \<close>
lemma add_sets_borel[measurable]:
  fixes x :: "'a :: real_normed_vector"
  shows "A' \<in> sets borel \<Longrightarrow> {a. a + x \<in> A'} \<in> sets borel"
    apply measurable
    apply (rule pred_sets2[where N=borel])
    apply blast
    using borel_measurable_const_add[of id borel x] apply (simp add: add.commute measurable_ident)
    done

lemma (in prob_space) conv_distr_kernel:
  assumes [measurable]: "X \<in> borel_measurable M"
  shows "transition_kernel borel borel (\<lambda>x A'. ((return borel x) \<star> (distr M borel X)) A')"
  apply (intro transition_kernel.intro)
     apply (subst convolution_emeasure)
             apply auto
       apply (simp add: prob_space_return[THEN prob_space.finite_measure])
      apply measurable
    apply (rule finite_measure_distr)
  apply (simp)
     apply (subst nn_integral_return)
       apply simp
      apply simp
      apply (subst emeasure_distr)
      apply simp
  apply simp
      apply measurable
       apply (rule pred_sets2[where N=borel])
        apply blast
     apply measurable
      apply (subst emeasure_distr)
    apply simp
    apply (simp add: add_sets_borel)
      apply measurable
       apply (rule pred_sets2[where N=borel])
        apply blast
    apply measurable
    by (metis measure_space sets_convolution space_borel space_convolution)

primrec phi where
"phi 0 I X = (\<lambda>x\<in>{I 0}. X (I 0))" |
"phi (Suc n) I X = (phi n I X)(I (Suc n) := sum X (I`{0..Suc n}))"

lemma phi_index: "inj_on I {0..n} \<Longrightarrow> k \<le> n \<Longrightarrow> phi n I X (I k) = sum X (I`{0..k})"
proof (induct n arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then consider "k = Suc n" | "k < Suc n"
    by linarith
  then show ?case
  proof cases
    case 1
    then show ?thesis by simp
  next
    case 2
    then have "I (Suc n) \<noteq> I k"
      using inj_on_contraD[OF Suc.prems(1)] by auto
    then show ?thesis
      apply auto
      using Suc.hyps 2 Suc.prems(1)
      by (metis Suc_leD atLeastatMost_subset_iff dual_order.refl inj_on_subset less_Suc_eq_le)
  qed
qed

lemma phi_notin: "ix \<notin> I ` {0..n} \<Longrightarrow> phi n I X ix = undefined"
  by (induct n, auto simp: image_iff)

lemma phi_restrict:
  assumes "inj_on I {0..n}"
  shows "phi n I x ix = phi n I (restrict x (I ` {0..n})) ix"
  using assms
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  consider "ix = I (Suc n)" | "ix \<in> I ` {0..n}" | "ix \<notin> I ` {0..Suc n}"
    using le_SucE by fastforce
  then show ?case
  proof cases
    case 1
    then show ?thesis
      by auto
  next
    case 2
    have "inj_on I {0..n}"
      using Suc.prems inj_on_subset by fastforce
    from 2 obtain k where "k \<le> n" "ix = I k"
      by force
    then show ?thesis
      apply (auto simp add: phi_index[OF \<open>inj_on I {0..n}\<close> \<open>k \<le> n\<close>])
      apply (rule sum.cong)
      by fastforce+
  next
    case 3
    then show ?thesis
      by (metis phi_notin)
  qed
qed

lemma sum_measurable_PiM[measurable]:
  "(\<lambda>x. \<Sum>i\<in>S. x i) \<in> borel_measurable (PiM S 
  (\<lambda>_. borel :: ('b:: {second_countable_topology,topological_comm_monoid_add} measure)))"
  apply (rule borel_measurable_sum)
  by simp

lemma phi_measurable[measurable]:
  assumes "inj_on I {0..n}"
  shows "phi n I \<in> PiM (I ` {0..n}) (\<lambda>_. borel) \<rightarrow>\<^sub>M PiM (I ` {0..n}) (\<lambda>_. borel :: ('b :: ordered_euclidean_space) measure)"
  using assms
proof (induct n arbitrary: I)
  case 0
  then show ?case
    apply simp
   apply (rule measurable_PiM_single)
    apply (smt (verit, best) PiE_I Pi_I UNIV_I singleton_iff space_borel)
    apply auto[1]
    done
next
  case (Suc n)
  then have inj: "inj_on I {0..n}"
    by (metis atLeast0_atMost_Suc inj_on_subset insert_subset order_refl)
  have I_notin: "I (Suc n) \<notin> I ` {0..n}"
  proof
    assume "I (Suc n) \<in> I ` {0..n}"
    then obtain k where k: "k \<in> {0..n}" "I (Suc n) = I k"
      by blast
    then have "k \<noteq> Suc n"
      using atLeast0AtMost lessThan_Suc_atMost by blast
    moreover have "k = Suc n"
      using k Suc.prems unfolding inj_on_def by auto
    ultimately show False
      by simp
  qed
  have phi_eq_comp: "phi (Suc n) I = 
  (\<lambda>(x,y). (phi n I x)(I(Suc n) := sum x (I`{0..n}) + y)) \<circ> (\<lambda>x. (restrict x (I ` {0..n}), x (I (Suc n))))"
    apply (auto simp add: fun_eq_iff atLeast0_atMost_Suc)
     apply (simp add: add.commute I_notin)
    using inj by (rule phi_restrict)
  then show ?case
    apply (subst phi_eq_comp)
    apply (rule measurable_comp[where N="Pi\<^sub>M (I ` {0..n}) (\<lambda>_. borel) \<Otimes>\<^sub>M borel"])
     apply measurable
      apply auto
    apply (simp add: atLeast0_atMost_Suc)
    apply measurable
    using Suc.hyps inj measurable_fst'' apply blast
    by measurable
qed

lemma PiM_borel_phi:
  assumes "inj_on I {0..n}"
  shows "sets (PiM (I ` {0..n}) (\<lambda>_. borel)) = sigma_sets (I`{0..n} \<rightarrow>\<^sub>E UNIV) 
  {phi n I -` X \<inter> (I`{0..n} \<rightarrow>\<^sub>E UNIV) | X. X \<in> prod_algebra (I ` {0..n}) (\<lambda>_. borel)}"
proof (simp add: sets_PiM_single, intro sigma_sets_eqI, goal_cases)
  case (1 a)
  then show ?case
    apply (intro sigma_sets.Basic)
    using assms proof (induct n)
    case 0
    then show ?case apply auto
      sorry
  next
    case (Suc n)
    then show ?case sorry
  qed
next
  case (2 b)
  then show ?case sorry
qed

text_raw \<open>\DefineSnippet{kernel_product_convolution}{\<close>
theorem (in prob_space) kernel_product_convolution:
  fixes X :: "('i :: linorder) \<Rightarrow> 'a \<Rightarrow> ('b :: ordered_euclidean_space)"
    and I :: "nat \<Rightarrow> 'i"
  assumes "indep_vars (\<lambda>_. borel) X (I ` {0..(n::nat)})" "inj_on I {0..n}"
  defines "S \<equiv> (\<lambda>k \<omega>. \<Sum>j \<in> {0..k}. X (I j) \<omega>)"
    and "K \<equiv> (\<lambda>k. kernel_of borel borel (\<lambda>x A'. ((return borel x) \<star> (distr M borel (X k))) A'))"
  shows "kernel_measure (PiK n I K) 0 = (\<Pi>\<^sub>M t\<in>I`{0..n}. distr M borel (X t))"
text_raw \<open>}%EndSnippet\<close>
proof -
  have X_measurable[measurable]: "\<And>k. k \<in> I ` {0..n} \<Longrightarrow> random_variable borel (X k)"
    using assms(1) unfolding indep_vars_def by auto
  then have "transition_kernel borel borel (\<lambda>x A'. ((return borel x) \<star> (distr M borel (X k))) A')"
    if "k \<in> I ` {0..n}" for k
    using that conv_distr_kernel by blast
  then have K_apply: "K k \<omega> A' = ((return borel \<omega>) \<star> (distr M borel (X k))) A'"
    if "k \<in> I ` {0..n}" "A' \<in> sets borel" for k A' \<omega>
    unfolding K_def using that by simp
  have "\<And>k. k \<in> {0..n} \<Longrightarrow> stochastic_kernel (K (I k))"
    apply (intro stochastic_kernel_altI)
    apply (subst K_apply; simp add: K_def)
    apply (subst convolution_emeasure)
           apply auto
       apply (simp add: prob_space_return[THEN prob_space.finite_measure])
     apply (rule finite_measure_distr)
    apply simp
    by (metis atLeastAtMost_iff  prob_space_distr[OF X_measurable] prob_space.emeasure_space_1
            imageI less_eq_nat.simps(1) space_borel space_distr)
  then interpret stochastic_kernel_family K I n
    unfolding K_def by (simp add: stochastic_kernel_family.intro)

  have stochastic_K: "stochastic_kernel (PiK n I K)"
    by (fact PiK_stochastic)
  then have PiK_0: "(PiK n I K) 0 (I`{0..n} \<rightarrow>\<^sub>E UNIV) = 1"
  proof -
    have 1: "I`{0..n} \<rightarrow>\<^sub>E UNIV = space (kernel_target (PiK n I K)) "
      by (simp add: space_PiM K_def)
    then show ?thesis
      apply (simp only: 1)
      apply (rule stochastic_kernel.kernel_space_eq_1[OF stochastic_K])
      apply (simp add: K_def)
      done
  qed
  show ?thesis
  proof (rule measure_eqI_generator_eq)
    let ?E = "{phi n I -` X \<inter> (I`{0..n} \<rightarrow>\<^sub>E UNIV) | X. X \<in> prod_algebra (I ` {0..n}) (\<lambda>_. borel)}"
    show "Int_stable ?E"
      by (smt (verit, best) Int_stable_def Int_stable_prod_algebra inf_commute inf_left_commute inf_right_idem mem_Collect_eq vimage_Int)
    show "?E \<subseteq> Pow (I`{0..n} \<rightarrow>\<^sub>E UNIV)"
      by fastforce
    show "sets (kernel_measure (PiK n I K) 0) = sigma_sets (I ` {0..n} \<rightarrow>\<^sub>E UNIV) ?E"
      by (simp add: K_def PiM_borel_phi[OF assms(2)])
    show "range (\<lambda>_. (I ` {0..n} \<rightarrow>\<^sub>E UNIV)) \<subseteq> ?E"
      apply simp
      sorry
    show " (\<Union>i. I ` {0..n} \<rightarrow>\<^sub>E UNIV) = I ` {0..n} \<rightarrow>\<^sub>E UNIV"
      by blast
    show "emeasure (kernel_measure (PiK n I K) 0) (I ` {0..n} \<rightarrow>\<^sub>E UNIV) \<noteq> \<infinity>"
      using stochastic_K sorry
    show "sets (Pi\<^sub>M (I ` {0..n}) (\<lambda>t. distr M borel (X t))) = sigma_sets (I ` {0..n} \<rightarrow>\<^sub>E UNIV) ?E"
      apply (subst sets_PiM_cong[where J="I ` {0..n}" and N="\<lambda>_. borel"])
      using PiM_borel_phi[OF assms(2)] by auto
    fix S :: "('i \<Rightarrow> 'b) set" assume "S \<in> ?E"
    then show "emeasure (kernel_measure (PiK n I K) 0) S = emeasure (Pi\<^sub>M (I ` {0..n}) (\<lambda>t. distr M borel (X t))) S"
    proof (induct n)
      case 0
      then show ?case apply auto
        sorry
    next
      case (Suc n)
      then show ?case sorry
    qed
  qed
qed

end
