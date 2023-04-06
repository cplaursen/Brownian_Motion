theory Kernel_Product
  imports Kernel
begin

text \<open> Klenke theorem 14.25 \<close>

definition kernel_product :: "('a, 'b) kernel \<Rightarrow> ('a \<times> 'b, 'c) kernel \<Rightarrow> ('a, 'b \<times> 'c) kernel" (infixr "(\<Otimes>\<^sub>K)" 90) where
"kernel_product K_1 K_2 \<equiv> kernel_of (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
  (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1))\<partial>kernel_measure K_1 \<omega>\<^sub>0)"

lemma kernel_product_source[simp]: "kernel_source (K_1 \<Otimes>\<^sub>K K_2) = kernel_source K_1"
  unfolding kernel_product_def by simp

lemma kernel_product_target[simp]: "kernel_target (K_1 \<Otimes>\<^sub>K K_2) = (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)"
  unfolding kernel_product_def by simp

definition kernel_product_partial :: "('a, 'b) kernel \<Rightarrow> ('b, 'c) kernel \<Rightarrow> ('a, 'b \<times> 'c) kernel" (infixr "(\<Otimes>\<^sub>P)" 90) where
"kernel_product_partial K_1 K_2 \<equiv> K_1 \<Otimes>\<^sub>K (kernel_of (kernel_source K_1 \<Otimes>\<^sub>M kernel_source K_2) (kernel_target K_2)
 (\<lambda>\<omega> A\<^sub>2. kernel K_2 (snd \<omega>) A\<^sub>2))"

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

lemma
  assumes "finite_measure M" "A \<in> sets M"
  shows "M (space M - A) = M (space M) - M A"
  using assms
  by (simp add: emeasure_compl finite_measure.emeasure_finite)

text \<open> Required for monotone convergence in the below theorem \<close>
lemma kernel_snd_measurable:
  fixes K :: "('a\<times>'b, 'c) kernel"
  defines "M2 \<equiv> kernel_target K"
  assumes "A \<in> sets (M1 \<Otimes>\<^sub>M M2)" "sets (kernel_source K) = sets (M0 \<Otimes>\<^sub>M M1)" "\<omega>\<^sub>0 \<in> space M0"
          "finite_kernel K"
  shows "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) \<in> borel_measurable M1"
proof -
  let ?G = "{x \<times> y | x y. x \<in> sets M1 \<and> y \<in> sets M2}"
  have sigma_G: "sigma_sets (space (M1 \<Otimes>\<^sub>M M2)) ?G = sets (M1 \<Otimes>\<^sub>M M2)"
    by (metis sets_pair_measure space_pair_measure)
  have "Int_stable ?G"
    using Int_stable_pair_measure_generator by blast
  moreover have "?G \<subseteq> Pow (space (M1 \<Otimes>\<^sub>M M2))"
    by (simp add: pair_measure_closed space_pair_measure)
  moreover have "A \<in> sigma_sets (space (M1 \<Otimes>\<^sub>M M2)) ?G"
    by (metis assms(2) sets_pair_measure space_pair_measure)
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
      using assms that by (measurable, auto)
    ultimately show "(\<lambda>w. kernel K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) \<in> borel_measurable M1"
      using xy apply auto
      apply measurable
        apply (smt (verit, ccfv_SIG) M2_def empty_Collect_eq mem_Collect_eq sets.empty_sets subsetI subset_antisym)
      using assms(3) assms(4) apply force
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
        by (metis assms(3,4) SigmaI sets_eq_imp_space_eq space_pair_measure)
      then have "finite_measure (kernel_measure K (\<omega>\<^sub>0, w))"
        by (simp add: finite_kernel.finite_measures assms(5))
      then have "kernel_measure K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) = 
          kernel_measure K (\<omega>\<^sub>0, w) (space M2) - kernel_measure K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}"
        unfolding M2_def apply (subst kernel_measure_space[THEN sym])+
        apply (rule emeasure_compl)
        using sigma_G compl M2_def w apply force
        by (simp add: finite_measure.emeasure_finite)
      then have "K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}) = K (\<omega>\<^sub>0, w) (space M2) - K (\<omega>\<^sub>0, w) {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A}"
        using kernel_measure_emeasure by metis
    } note diff = this
    have space_eq: "{\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> space (M1 \<Otimes>\<^sub>M M2)} = space M2" if "w \<in> space M1" for w
      by (simp add: that space_pair_measure)
    have "(\<lambda>w. K (\<omega>\<^sub>0, w) (space M2 - {\<omega>\<^sub>2. (w, \<omega>\<^sub>2) \<in> A})) \<in> borel_measurable M1"
      apply (subst measurable_cong[OF diff])
       apply simp
      unfolding M2_def using assms(3) apply measurable
      using assms(4) apply simp
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
        using assms(4) sets_eq_imp_space_eq[OF assms(3)] space_pair_measure by blast
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

theorem kernel_product_transition_kernel:
  fixes K_1 :: "('a, 'b) kernel"
    and K_2 :: "('a\<times>'b, 'c) kernel"
  assumes finite: "finite_kernel K_1" "finite_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
    shows"transition_kernel (kernel_source K_1) (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2)
    (\<lambda>\<omega>\<^sub>0 A. \<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. indicator A (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K_2 (\<omega>\<^sub>0, \<omega>\<^sub>1)) \<partial>kernel_measure K_1 \<omega>\<^sub>0)"
  (is "transition_kernel ?\<Omega>\<^sub>1 ?\<Omega>\<^sub>2 ?\<kappa>")
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
    unfolding kernel_measure_altdef apply simp
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
       apply (intro transition_kernelI)
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
      by (fact finite_kernel_finite[OF finite(2)])
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
          apply (metis infinity_ennreal_def top.not_eq_extremum sigma_finite kernel_measure_emeasure)
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
    apply (intro prob_spaceI)
    by (auto simp: kernel_measure_emeasure)
qed

(* CARBON COPY OF THE ABOVE *)
lemma kernel_product_substochastic:    
  assumes substochastic: "substochastic_kernel K_1" "substochastic_kernel K_2"
      and eq: "sets (kernel_source K_2) = sets (kernel_source K_1 \<Otimes>\<^sub>M kernel_target K_1)"
      and nonempty: "space (kernel_target K_1 \<Otimes>\<^sub>M kernel_target K_2) \<noteq> {}" 
        (* Could remove assumption with changes to substochastic locale *)
    shows "substochastic_kernel (K_1 \<Otimes>\<^sub>K K_2)"
proof (rule substochastic_kernelI)
  fix \<omega> assume *: "\<omega> \<in> space (kernel_source (K_1 \<Otimes>\<^sub>K K_2))"
  have "finite_kernel K_1" "finite_kernel K_2"
    using assms substochastic_kernel.axioms(1) by blast+
  then have "(K_1 \<Otimes>\<^sub>K K_2) \<omega> (space (kernel_target (K_1 \<Otimes>\<^sub>K K_2))) \<le> \<integral>\<^sup>+ \<omega>\<^sub>1. emeasure (kernel_measure K_2 (\<omega>, \<omega>\<^sub>1)) (space (kernel_target K_2)) \<partial>kernel_measure K_1 \<omega>"
    apply (subst kernel_prod_apply)
    using * apply (simp_all add: assms)
    apply (simp add: space_pair_measure indicator_times)
    apply (subst(2) nn_integral_eq_simple_integral)
     apply auto
    apply (rule nn_integral_mono)
    by simp
  also have "... \<le>  \<integral>\<^sup>+ \<omega>\<^sub>1. 1 \<partial>kernel_measure K_1 \<omega>"
    apply (rule nn_integral_mono)
    using substochastic
    by (metis kernel_measure_emeasure kernel_not_space_zero linordered_nonzero_semiring_class.zero_le_one subprob_space.subprob_emeasure_le_1 substochastic_kernel.subprob_measures)
  also have "... \<le> 1"
    apply simp
    using substochastic
    by (metis * kernel_product_source subprob_space.subprob_emeasure_le_1 substochastic_kernel.subprob_measures)
  finally show "subprob_space (kernel_measure (K_1 \<Otimes>\<^sub>K K_2) \<omega>)"
    by (auto intro: subprob_spaceI simp: kernel_measure_emeasure nonempty)
qed

section \<open> Kernel semidirect product \<close>

lemma arg_cong3: "\<lbrakk>a = d; b = e; c = f\<rbrakk> \<Longrightarrow> g a b c = g d e f"
  by simp

lemma semidirect_product_unique:
  assumes space: "x \<in> space M" "y \<in> space M"
    and finite: "finite_measure M" "finite_kernel K"
    and sets: "sets M = sets (kernel_source K)"
  shows "kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) x = kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) y"
 (* Disgusting proof *)
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

definition kernel_semidirect_product :: "'a measure \<Rightarrow> ('a, 'b) kernel \<Rightarrow> ('a \<times> 'b) measure" (infixr "(\<Otimes>\<^sub>S)" 70)
  where "M \<Otimes>\<^sub>S K = kernel_measure (emeasure_kernel M M \<Otimes>\<^sub>P K) (SOME \<omega>. \<omega> \<in> space (kernel_source K))"

lemma space_kernel_semidirect_product[simp]: "space (M \<Otimes>\<^sub>S K) = (space M \<times> space (kernel_target K))"
  unfolding kernel_semidirect_product_def by (simp add: space_pair_measure)

lemma sets_kernel_semidirect_product[measurable]: "sets (M \<Otimes>\<^sub>S K) = sets (M \<Otimes>\<^sub>M (kernel_target K))"
  unfolding kernel_semidirect_product_def 
  by (simp add: kernel_product_partial_def)

lemma kernel_semidirect_product_measurable[measurable]: 
  "f \<in> M \<Otimes>\<^sub>M (kernel_target K) \<rightarrow>\<^sub>M M' \<longleftrightarrow> f \<in> M \<Otimes>\<^sub>S K \<rightarrow>\<^sub>M M'"
  using measurable_cong_sets[OF sets_kernel_semidirect_product] by blast

locale finite_measure_kernel = K?: finite_kernel K + M?: finite_measure M
  for K :: "('a, 'b) kernel" and M :: "'a measure" +
  assumes sets_eq: "sets (kernel_source K) = sets M"
      and nonempty: "space M \<noteq> {}"
begin

lemma space_eq: "space (kernel_source K) = space M"
  by (fact sets_eq_imp_space_eq[OF sets_eq])

lemma emeasure_times_semidirect_product: 
  assumes "A \<in> sets M" "B \<in> sets (kernel_target K)"
  shows "emeasure (M \<Otimes>\<^sub>S K) (A \<times> B) = \<integral>\<^sup>+\<omega>\<^sub>1 \<in> A. K \<omega>\<^sub>1 B \<partial>M"
  unfolding kernel_semidirect_product_def apply (simp add: kernel_measure_emeasure)
  apply (subst kernel_prod_partial_apply)
  apply (simp add: emeasure_kernel_finite finite_measure_axioms)
  apply (simp add: finite_kernel_axioms)
  using sets_eq apply simp
  using nonempty apply (simp add: space_eq some_in_eq)
  using assms(1,2) apply simp
   apply (simp add: space_eq)
   apply (subst kernel_measure_emeasure_kernel)
  using some_in_eq nonempty apply blast
   apply (rule nn_integral_cong)
   apply (simp add: indicator_times)
  apply (simp add: assms(2) kernel_measure_emeasure mult.commute nn_integral_cmult_indicator)
  done

lemma kernel_semidirect_product_finite: "finite_measure (M \<Otimes>\<^sub>S K)"
  apply (intro finite_measureI)
  apply (simp add: space_pair_measure)
  apply (subst emeasure_times_semidirect_product; simp)
  oops

lemma indicator_diff_ennreal: "indicator (A - B) x = indicator A x * (1 - indicator B x ::ennreal)"
  by (simp add: indicator_def)

lemma kernel_Fubini:
  assumes f[measurable]: "f \<in> borel_measurable (M \<Otimes>\<^sub>M (kernel_target K))"
  shows "(\<integral>\<^sup>+\<omega>. f \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = (\<integral>\<^sup>+\<omega>\<^sub>1. (\<integral>\<^sup>+\<omega>\<^sub>2. f (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M)"
using f proof induct
  case (cong f g)
  then have "\<And>x y. x \<in> space M \<Longrightarrow> y \<in> space (kernel_target K) \<Longrightarrow> f (x,y) = g (x,y)"
    using space_pair_measure by fast
  then show ?case
    by (smt (verit, best) cong.hyps(3) cong.hyps(4) kernel_measure_space nn_integral_cong
        sets_eq_imp_space_eq sets_kernel_semidirect_product)
next
  case (set A)
  then show ?case
    apply (subst nn_integral_indicator)
    using sets_kernel_semidirect_product apply blast
    unfolding kernel_semidirect_product_def 
    apply (subst kernel_measure_emeasure)
    apply (subst kernel_prod_partial_apply)
    using emeasure_kernel_finite finite_measure_axioms apply blast
    using finite_kernel_axioms apply blast
       apply (simp add: sets_eq)
      apply (simp add: nonempty some_in_eq space_eq)
     apply simp
    apply (subst kernel_measure_emeasure_kernel)
     apply (simp add: nonempty some_in_eq space_eq)
    ..
next
  case (mult u v)
  have L: "(\<integral>\<^sup>+ \<omega>. v * u \<omega> \<partial>(M \<Otimes>\<^sub>S K)) = v * (\<integral>\<^sup>+ \<omega>. u \<omega> \<partial>(M \<Otimes>\<^sub>S K))"
    using nn_integral_cmult kernel_semidirect_product_measurable mult.hyps(2) by blast
  have "(\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v * u (\<omega>\<^sub>1, \<omega>\<^sub>2) \<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) = \<integral>\<^sup>+ \<omega>\<^sub>1. v * (\<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1) \<partial>M"
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
  also have "... = (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. v (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M) + (\<integral>\<^sup>+ \<omega>\<^sub>1. \<integral>\<^sup>+ \<omega>\<^sub>2. u (\<omega>\<^sub>1, \<omega>\<^sub>2)\<partial>kernel_measure K \<omega>\<^sub>1 \<partial>M)"
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

text \<open> Klenke Corollary 14.27 \<close>
(*
corollary kernel_finite_product:
  assumes "\<forall>i \<in> {1..(n::nat)}. sets (kernel_source (K (i - 1))) = sets (M (i - 1)) \<and> sets (kernel_target (K i)) = sets (M i) \<and> stochastic_kernel (K i)"
  shows undefined
  oops
*)

end