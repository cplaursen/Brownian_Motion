theory Markov_Semigroup
  imports Kernel_Composition "List-Index.List_Index"
begin

find_consts "('a :: ord) list" "'a set"

text \<open> Klenke definition 14.42 \<close>

locale consistent_family =
  fixes I :: "'i :: linorder set"
    and K :: "'i \<Rightarrow> 'i \<Rightarrow> 'a hkernel"
    and M :: "'a measure"
  assumes space: "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i < j\<rbrakk> \<Longrightarrow> hkernel_space (K i j) = M"
    and comp: "\<And>i j k. \<lbrakk>i \<in> I; j \<in> I; k \<in> I; i < j; j < k\<rbrakk> \<Longrightarrow> K i j \<circ>\<^sub>K K j k = K i k"
    and stochastic_family: "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i < j\<rbrakk> \<Longrightarrow> stochastic_kernel (K i j)"

text \<open> Klenke definition 14.43 \<close>

(* Klenke specifies that K can range over an additive semigroup, but this
  precludes the below lemma 14.44 where he subtracts elements from the semigroup *)

locale markov_semigroup =
  fixes K :: "real \<Rightarrow> 'a hkernel"
    and M :: "'a measure"
  assumes space_eq_M: "\<And>i. i \<ge> 0 \<Longrightarrow> hkernel_space (K i) = M"
      and init: "\<And>\<omega>. \<omega> \<in> space (kernel_source (K 0))
   \<Longrightarrow> kernel_measure (K 0) \<omega> = return (kernel_source (K 0)) \<omega>"
      and comp_sum: "\<And>s t. \<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> K s \<circ>\<^sub>K K t = K (s + t)"
      and stochastic: "\<And>i. i \<ge> 0 \<Longrightarrow> stochastic_kernel (K i)"
begin

lemma kernel_comp_commute: "\<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> K s \<circ>\<^sub>K K t = K t \<circ>\<^sub>K K s"
  by (simp add: add.commute comp_sum)

text \<open> Klenke lemma 14.44 \<close>
lemma (in markov_semigroup) consistent: "consistent_family {0..} (\<lambda>x y. K (y-x)) M"
  by (intro consistent_family.intro; simp add: stochastic comp_sum space_eq_M)
end

locale real_consistent_family = consistent_family I for I:: "real set" +
  assumes I_nonneg: "I \<subseteq> {0..}"
      and I_zero: "0 \<in> I"
begin

section \<open> Infinite product kernel \<close>

text \<open> From the textbook: Let I \<subseteq> [0, \<infinity>) with 0 \<in> I, and let \<kappa> s t be a consistent family of 
  stochastic kernels on the Polish space E.
  Then there exists a kernel \<kappa> from borel to PiM I (\<lambda>_. borel) such that, for
  all x \<in> E and for any choice of finitely many numbers l we have

  \<kappa> x \<circ> X_J^{-1} = (\<delta>_x \<otimes> \<Otimes> (n-1) (\<lambda>k. \<kappa> (l!k) (l!Suc k)

  Where X_J is the product embedding.

  We're going to define this as a family of infinite product measures. We fix x \<in> E and show that
  the above defines a projective family, and then define the target as the projective limit.

\<close>

lemma sorted_list_of_set_nth_mem: 
  assumes "finite J" "n < card J"
  shows "sorted_list_of_set J ! n \<in> J"
  by (metis assms nth_mem length_sorted_list_of_set sorted_list_of_set(1))


definition P :: "'a \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> 'a) measure" where
"P x J \<equiv>
  let l = sorted_list_of_set J
  in (if J = {0} then distr (return M x) (PiM J (\<lambda>_. M)) (\<lambda>x. (\<lambda>y\<in>{0}. x)) else
  distr (return M x \<Otimes>\<^sub>S (PiK (length l - 2) (\<lambda>x. x) (\<lambda>n. K (l!n) (l!Suc n))))
           (PiM J (\<lambda>_. M)) (\<lambda>(x, y) ix. case index l ix of 0 \<Rightarrow> x | Suc n \<Rightarrow> y n))"

definition P' :: "'a \<Rightarrow> real set \<Rightarrow> (real \<Rightarrow> 'a) measure" where
"P' x J = (if 0 \<notin> J then distr (P x (J \<union> {0})) (PiM J (\<lambda>_. M)) (\<lambda>f. restrict f J) else P x J)"

text \<open> Need to add a special case for P' x {0} -- should just be return M x lifted to PiM \<close>

lemma P_projection_measurable:
  fixes J defines "l \<equiv> sorted_list_of_set J"
  assumes "J \<subseteq> I" "finite J" "card J \<ge> 2"
  shows "(\<lambda>(x, y) ix. case index l ix of 0 \<Rightarrow> x | Suc n \<Rightarrow> y n) \<in> 
  (return M x \<Otimes>\<^sub>S (PiK (length l - 2) (\<lambda>x. x) (\<lambda>n. K (l!n) (l!Suc n)))) \<rightarrow>\<^sub>M (PiM J (\<lambda>_. M))"
  (is "?f \<in> (return M x \<Otimes>\<^sub>S ?PiK) \<rightarrow>\<^sub>M (PiM J (\<lambda>_. M))")
proof (rule measurable_PiM_single)
  show "?f \<in> space (return M x \<Otimes>\<^sub>S ?PiK) \<rightarrow> J \<rightarrow>\<^sub>E space M"
  proof (intro Pi_I, safe, goal_cases)
    case (1 a b x)
    then have "a \<in> space M"
      by simp
    moreover have "space (kernel_target ?PiK) = {0..length l - 2} \<rightarrow>\<^sub>E (space M)"
      apply auto
      sorry
    ultimately show ?case
      sorry
  next
    case (2 a b x)
    then show ?case sorry
  qed
  oops
(*  apply (simp add: kernel_semidirect_product_measurable)
  apply measurable
  apply (rule measurable_PiM_single)
   apply (subst PiM_cong[where J="{0..length l - 2}" and N = "\<lambda>_. M"])
     apply simp
    apply (subst space)
  using assms sorted_list_of_set_nth_mem apply fastforce
  using assms sorted_list_of_set_nth_mem apply fastforce
  apply (metis assms(1,4) Suc_lessI atLeastAtMost_iff diff_Suc_Suc diff_less lessI less_imp_diff_less linorder_neqE_nat linorder_not_le numeral_2_eq_2 sorted_list_of_set.length_sorted_key_list_of_set sorted_wrt_iff_nth_less strict_sorted_list_of_set zero_less_Suc)
    apply simp
   apply (simp add: space_pair_measure space_PiM)
   apply (intro funcsetI)
   apply (intro PiE_I)
  subgoal for x xa
    apply (cases "index l xa")
     apply auto[1]
    unfolding extensional_funcset_def using assms apply auto
    apply (rule Pi_mem[where A = "{0..card J -2}" and B = "\<lambda>_. space M"])
     apply simp
    apply simp
    using set_sorted_list_of_set[OF assms(3)]
    by (metis Suc_diff_Suc Suc_le_lessD Suc_pred dual_order.strict_trans1 index_less_size_conv less_Suc_eq_le numeral_2_eq_2 pos2 sorted_list_of_set.length_sorted_key_list_of_set)
  subgoal for x xa
    using index_size_conv[of l "length l" xa] sledgehammer*)

lemma P'_projective_family: "x \<in> space M \<Longrightarrow> projective_family I (P' x) (\<lambda>_. M)"
proof (intro projective_family.intro)
  fix J H assume  "finite H" "J \<subseteq> H" "H \<subseteq> I" "x \<in> space M"
  then show "P' x J = distr (P' x H) (Pi\<^sub>M J (\<lambda>_. M)) (\<lambda>f. restrict f J)"
  proof induct
    case empty
    then show ?case sorry
  next
    case (insert x F)
    then show ?case sorry
  qed
next
  show "\<And>J. x \<in> space M \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> prob_space (P' x J)"
    sorry
qed

lemma "transition_kernel M (PiM I (\<lambda>_. M)) (\<lambda>\<omega>. emeasure (projective_family.lim I (P' \<omega>) (\<lambda>_. M)))"
proof (intro transition_kernel.intro, goal_cases)
  case (1 A')
  then show ?case sorry
next
  case (2 \<omega>)
  then show ?case
    by (metis P'_projective_family measure_space projective_family.sets_lim projective_family.space_lim)
qed

definition lim_kernel :: "('a, real \<Rightarrow> 'a) kernel" where
"lim_kernel \<equiv> kernel_of M (PiM I (\<lambda>_. M)) (\<lambda>\<omega>. emeasure (projective_family.lim I (P' \<omega>) (\<lambda>_. M)))"

end

sublocale markov_semigroup \<subseteq> real_consistent_family "\<lambda>x y. K (y-x)" M "{0..}"
  by (simp add: consistent real_consistent_family_axioms_def real_consistent_family_def)

end
