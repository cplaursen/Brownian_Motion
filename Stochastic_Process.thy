theory Stochastic_Process
  imports "HOL-Probability.Probability" "Dyadic_Interval"
begin

text \<open> A stochastic process is an indexed collection of random variables. For compatibility with 
  product_prob_space we don't mention the index set I in the assumptions. \<close>

text_raw \<open>\DefineSnippet{stochastic_process}{\<close>
locale stochastic_process = prob_space +
  fixes M' :: "'b measure"
    and I :: "'t set"
    and X :: "'t \<Rightarrow> 'a \<Rightarrow> 'b"
  assumes random_process[measurable]: "\<And>i. random_variable M' (X i)"
text_raw \<open>}%EndSnippet\<close>

sublocale stochastic_process \<subseteq> product: product_prob_space "(\<lambda>t. distr M M' (X t))"
  using prob_space_distr random_process by (blast intro: product_prob_spaceI)

lemma (in prob_space) stochastic_processI:
  assumes "\<And>i. random_variable M' (X i)"
    shows "stochastic_process M M' X"
  by (simp add: assms prob_space_axioms stochastic_process_axioms.intro stochastic_process_def)

text_raw \<open>\DefineSnippet{stochastic_process_typedef}{\<close>
typedef ('t, 'a, 'b) stochastic_process =
 "{(M :: 'a measure, M' :: 'b measure, I :: 't set, X :: 't \<Rightarrow> 'a \<Rightarrow> 'b).
   stochastic_process M M' X}"
text_raw \<open>}%EndSnippet\<close>
proof
  show "(return (sigma UNIV {{}, UNIV}) x, sigma UNIV UNIV, UNIV, \<lambda>_ _. c) \<in>
       {(M, M', I, X). stochastic_process M M' X}" for x :: 'a and c :: 'b
    by (simp add: prob_space_return prob_space.stochastic_processI)
qed

setup_lifting type_definition_stochastic_process

lift_definition proc_source :: "('t,'a,'b) stochastic_process \<Rightarrow> 'a measure"
is "fst" .

interpretation proc_source: prob_space "proc_source X"
  by (induction, simp add: proc_source_def Abs_stochastic_process_inverse case_prod_beta' stochastic_process_def)

lift_definition proc_target :: "('t,'a,'b) stochastic_process \<Rightarrow> 'b measure"
is "fst \<circ> snd" .

lift_definition proc_index :: "('t,'a,'b) stochastic_process \<Rightarrow> 't set"
is "fst \<circ> snd \<circ> snd" .

lift_definition process :: "('t,'a,'b) stochastic_process \<Rightarrow> 't \<Rightarrow> 'a \<Rightarrow> 'b"
is "snd \<circ> snd \<circ> snd" .

declare [[coercion process]]

lemma stochastic_process_construct [simp]: "stochastic_process (proc_source X) (proc_target X) (process X)"
  by (transfer, force)

interpretation stochastic_process "proc_source X" "proc_target X" "proc_index X" "process X"
  by simp

text \<open> Here we construct a process on a given index set. For this we need to produce measurable
  functions for indices outside the index set; we use the constant function, but it needs to point at
  an element of the target set to be measurable. \<close>

lift_definition process_of :: "'a measure \<Rightarrow> 'b measure \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('t,'a,'b) stochastic_process"
  is "\<lambda> M M' I X \<omega>. if (\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M') \<and> prob_space M \<and> \<omega> \<in> space M'
  then (M, M', I, (\<lambda>t. if t \<in> I then X t else (\<lambda>_. \<omega>)))
  else (return (sigma UNIV {{}, UNIV}) (SOME x. True), sigma UNIV UNIV, I, \<lambda>_ _. \<omega>)"
  by (simp add: prob_space.stochastic_processI prob_space_return)

lemma index_process_of[simp]: "proc_index (process_of M M' I X \<omega>) = I"
  by (transfer, auto)

lemma
  assumes "\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'" "prob_space M" "\<omega> \<in> space M'"
  shows
    source_process_of[simp]: "proc_source (process_of M M' I X \<omega>) = M" and
    target_process_of[simp]: "proc_target (process_of M M' I X \<omega>) = M'" and
    process_process_of[simp]: "process (process_of M M' I X \<omega>) = (\<lambda>t. if t \<in> I then X t else (\<lambda>_. \<omega>))"
  using assms by (transfer, auto)+

lemma process_of_apply:
  assumes "\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'" "prob_space M" "\<omega> \<in> space M'" "t \<in> I"
  shows "process (process_of M M' I X \<omega>) t = X t"
  using assms by (meson process_process_of)

text \<open> We define the finite-dimensional distributions of our process. \<close>

text_raw \<open>\DefineSnippet{distributions}{\<close>
lift_definition distributions :: "('t, 'a, 'b) stochastic_process \<Rightarrow> 't set \<Rightarrow> ('t \<Rightarrow> 'b) measure"
is "\<lambda>(M, M', _, X) T. (\<Pi>\<^sub>M t\<in>T. distr M M' (X t))"
text_raw \<open>}%EndSnippet\<close> .

lemma distributions_altdef: "distributions X T = (\<Pi>\<^sub>M t\<in>T. distr (proc_source X) (proc_target X) (X t))"
  by (transfer, auto)

lemma prob_space_distributions: "prob_space (distributions X J)"
  unfolding distributions_altdef
  by (simp add: prob_space_PiM proc_source.prob_space_distr random_process)

lemma sets_distributions: "sets (distributions X J) = sets (PiM J (\<lambda>_. (proc_target X)))"
  by (transfer, auto cong: sets_PiM_cong)

lemma space_distributions: "space (distributions X J) = (\<Pi>\<^sub>E i\<in>J. space (proc_target X))"
  by (transfer, auto simp add: space_PiM)

lemma emeasure_distributions:
  assumes "finite J" "\<And>j. j\<in>J \<Longrightarrow> A j \<in> sets (proc_target X)"
  shows "emeasure (distributions X J) (Pi\<^sub>E J A) = (\<Prod>j\<in>J. emeasure (distr (proc_source X) (proc_target X) (X j)) (A j))"
  by (simp add: assms(1) assms(2) distributions_altdef product.emeasure_PiM)

interpretation projective_family "(proc_index X)" "distributions X" "(\<lambda>_. proc_target X)"
proof (intro projective_family.intro)
  fix J and H
  let ?I = "proc_index X"
  and ?M = "proc_source X"
  and ?M' = "proc_target X"
  assume *: "J \<subseteq> H" "finite H" "H \<subseteq> ?I"
  then have "J \<subseteq> ?I"
    by simp
  show "distributions X J = distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)"
  proof (rule measure_eqI)
    show "sets (distributions X J) = sets (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J))"
      by (simp add: sets_distributions)
    fix S assume "S \<in> sets (distributions X J)"
    then have in_sets: "S \<in> sets (PiM J (\<lambda>_. ?M'))"
      by (simp add: sets_distributions)
    have prod_emb_distr: "(prod_emb H (\<lambda>_. ?M') J S) = (prod_emb H (\<lambda>t. distr ?M ?M' (X t)) J S)"
      by (simp add: prod_emb_def)
    have "emeasure (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)) S =
          emeasure (distributions X H) (prod_emb H (\<lambda>_. ?M') J S)"
      apply (rule emeasure_distr_restrict)
      by (simp_all add: "*" sets_distributions in_sets)
    also have "... = emeasure (distributions X J) S"
      unfolding distributions_altdef
        using *(1,2) in_sets prod_emb_distr by force
    finally show "emeasure (distributions X J) S 
                = emeasure (distr (distributions X H) (Pi\<^sub>M J (\<lambda>_. ?M')) (\<lambda>f. restrict f J)) S"
      by argo
  qed
qed (rule prob_space_distributions)

locale polish_stochastic = stochastic_process M "borel :: 'b::polish_space measure" I X
  for M and I and X

(*
sublocale polish_stochastic \<subseteq> polish_projective I distributions
  by (simp add: polish_projective.intro projective_family_axioms) *)

lemma distributed_cong_random_variable:
  assumes "M = K" "N = L" "AE x in M. X x = Y x" "X \<in> M \<rightarrow>\<^sub>M N" "Y \<in> K \<rightarrow>\<^sub>M L" "f \<in> borel_measurable N"
  shows "distributed M N X f \<longleftrightarrow> distributed K L Y f"
  using assms by (auto simp add: distributed_def distr_cong_AE)

lemma (in prob_space) indep_sets_indep_set:
  assumes "indep_sets F I" "i \<in> I" "j \<in> I" "i \<noteq> j"
  shows "indep_set (F i) (F j)"
  unfolding indep_set_def
proof (rule indep_setsI)
  show "(case x of True \<Rightarrow> F i | False \<Rightarrow> F j) \<subseteq> events" for x
    using assms by (auto split: bool.split simp: indep_sets_def)
  fix A J assume *: "J \<noteq> {}" "J \<subseteq> UNIV" "\<forall>ja\<in>J. A ja \<in> (case ja of True \<Rightarrow> F i | False \<Rightarrow> F j)"
  {
    assume "J = UNIV"
    then have "indep_sets F I" "{i,j} \<subseteq> I" "{i, j} \<noteq> {}" "finite {i,j}" "\<forall>x \<in> {i,j}. (\<lambda>x. if x = i then A True else A False) x \<in> F x"
      using * assms apply simp_all
      by (simp add: bool.split_sel)
    then have "prob (\<Inter>j\<in>{i, j}. if j = i then A True else A False) = (\<Prod>j\<in>{i, j}. prob (if j = i then A True else A False))"
      by (rule indep_setsD)
    then have "prob (A True \<inter> A False) = prob (A True) * prob (A False)"
      using assms by (auto simp: ac_simps)
  } note X = this
  consider "J = {True, False}" | "J = {False}" | "J = {True}"
    using *(1,2) unfolding UNIV_bool by blast
  then show "prob (\<Inter> (A ` J)) = (\<Prod>j\<in>J. prob (A j))"
    using X by (cases; auto)
qed

lemma (in prob_space) indep_vars_indep_var:
  assumes "indep_vars M' X I" "i \<in> I" "j \<in> I" "i \<noteq> j"
  shows "indep_var (M' i) (X i) (M' j) (X j)"
  using assms unfolding indep_vars_def indep_var_eq
  by (meson indep_sets_indep_set)

text \<open> For all sorted lists of indices, the increments specified by this list are independent \<close>


text_raw \<open>\DefineSnippet{indep_increments}{\<close>
definition (in prob_space) "indep_increments M' X I \<longleftrightarrow>
  (\<forall>l. set l \<subseteq> I \<and> sorted l \<and> length l \<ge> 2 \<longrightarrow>
     indep_vars (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l})"
text_raw \<open>}%EndSnippet\<close>

lemma (in prob_space) indep_incrementsE:
  assumes "indep_increments M' X I"
      and "set l \<subseteq> I \<and> sorted l \<and> length l \<ge> 2"
    shows "indep_vars (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}"
  using assms unfolding indep_increments_def by blast

lemma (in prob_space) indep_incrementsI:
  assumes "\<And>l. set l \<subseteq> I \<Longrightarrow> sorted l \<Longrightarrow> length l \<ge> 2 \<Longrightarrow>
   indep_vars (\<lambda>_. M') (\<lambda>k v. X (l!k) v - X (l!(k-1)) v) {1..<length l}"
  shows "indep_increments M' X I"
  unfolding indep_increments_def using assms by blast

lemma (in prob_space) indep_increments_indep_var:
  assumes "indep_increments M' X I" "h \<in> I" "j \<in> I" "k \<in> I" "h \<le> j" "j \<le> k"
  shows "indep_var M' (\<lambda>v. X j v - X h v) M' (\<lambda>v. X k v - X j v)"
proof -
  let ?l = "[h,j,k]"
  have l: "set ?l \<subseteq> I \<and> sorted ?l \<and> 2 \<le> length ?l"
    using assms by auto
  have 1: "indep_vars (\<lambda>_. M') (\<lambda>k v. X (?l!k) v - X (?l!(k-1)) v) {1..<length ?l}"
    by (fact indep_incrementsE[OF assms(1) l])
  have 2: "1 \<in> {1..<length ?l}"
    by simp
  have 3: "2 \<in> {1..<length ?l}"
    by simp
  have 4: "(1 :: nat) \<noteq> 2"
    by simp
  from indep_vars_indep_var[OF 1 2 3 4] show "indep_var M' (\<lambda>v. X j v - X h v) M' (\<lambda>v. X k v - X j v)"
    by simp
qed

text_raw \<open>\DefineSnippet{stationary_increments}{\<close>
definition (in prob_space) "stationary_increments M' X \<longleftrightarrow>
(\<forall>t1 t2 k. t1 > 0 \<and> t2 > 0 \<and> k > 0 \<longrightarrow> 
     distr M M' (\<lambda>v. X (t1 + k) v - X t1 v) = distr M M' (\<lambda>v. X (t2 + k) v - X t2 v))"
text_raw \<open>}%EndSnippet\<close>

text \<open> Processes on the same source measure space, with the same index space, but not necessarily the same
  target measure since we only care about the measurable target space, not the measure \<close>

text_raw \<open>\DefineSnippet{compatible}{\<close>
definition compatible :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
"compatible X Y \<longleftrightarrow> proc_source X = proc_source Y \<and> sets (proc_target X) = sets (proc_target Y)
  \<and> proc_index X = proc_index Y"
text_raw \<open>}%EndSnippet\<close>

lemma compatibleI:
  assumes "proc_source X = proc_source Y" "sets (proc_target X) = sets (proc_target Y)"
          "proc_index X = proc_index Y"
  shows "compatible X Y"
  unfolding compatible_def using assms by simp

lemma
  assumes "compatible X Y"
  shows
    compatible_source: "proc_source X = proc_source Y" and
    compatible_target: "sets (proc_target X) = sets (proc_target Y)" and
    compatible_index: "proc_index X = proc_index Y"
  using assms unfolding compatible_def by blast+

lemma compatible_refl [simp]: "compatible X X"
  unfolding compatible_def by blast

lemma compatible_sym: "compatible X Y \<Longrightarrow> compatible Y X"
  unfolding compatible_def by argo

lemma compatible_trans:
  assumes "compatible X Y" "compatible Y Z"
    shows "compatible X Z"
  using assms unfolding compatible_def by argo

lemma compatible_process_of:
  assumes measurable: "\<forall>t \<in> I. X t \<in> M \<rightarrow>\<^sub>M M'" "\<forall>t \<in> I. Y t \<in> M \<rightarrow>\<^sub>M M'" 
      and "prob_space M" "a \<in> space M'" "b \<in> space M'"
  shows "compatible (process_of M M' I X a) (process_of M M' I Y b)"
  unfolding compatible_def using assms by force

text_raw \<open>\DefineSnippet{modification}{\<close>
definition modification :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
"modification X Y \<longleftrightarrow> compatible X Y \<and> (\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x)"
text_raw \<open>}%EndSnippet\<close>

lemma modificationI:
  assumes "compatible X Y" "(\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x)"
  shows "modification X Y"
  unfolding modification_def using assms by blast

lemma modificationD:
  assumes "modification X Y"
  shows "compatible X Y"
    and "\<And>t. t \<in> proc_index X \<Longrightarrow> AE x in proc_source X. X t x = Y t x"
  using assms unfolding modification_def by blast+

lemma modification_null_set:
  assumes "modification X Y" "t \<in> proc_index X"
  obtains N where "{x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N \<and> N \<in> null_sets (proc_source X)"
proof -
  from assms have "AE x in proc_source X. X t x = Y t x"
    by (simp add: modificationD(2))
  then have "\<exists>N\<in>null_sets (proc_source X). {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N"
    by (subst eventually_ae_filter[symmetric])
  then show ?thesis
    using that by blast
qed

lemma modification_refl [simp]: "modification X X"
  by (simp add: modificationI)

lemma modification_sym: "modification X Y \<Longrightarrow> modification Y X"
proof (rule modificationI, safe)
  assume *: "modification X Y"
  then show compat: "compatible Y X"
    using compatible_sym modificationD(1) by blast
  fix t assume "t \<in> proc_index Y"
  then have "t \<in> proc_index X"
    using compatible_index[OF compat] by blast
  have "AE x in proc_source Y. X t x = Y t x"
    using modificationD(2)[OF * \<open>t \<in> proc_index X\<close>] compatible_source[OF compat] by argo
  then show "AE x in proc_source Y. Y t x = X t x"
    by force
qed

lemma modification_trans:
  assumes "modification X Y" "modification Y Z"
  shows "modification X Z"
proof (intro modificationI, safe)
  show "compatible X Z"
    using compatible_trans modificationD(1) assms by blast
  fix t assume t: "t \<in> proc_index X"
  have XY: "AE x in proc_source X. process X t x = process Y t x"
    by (fact modificationD(2)[OF assms(1) t])
  have "t \<in> proc_index Y" "proc_source X = proc_source Y"
    using compatible_index compatible_source assms(1) modificationD(1) t by blast+
  then have "AE x in proc_source X. process Y t x = process Z t x"
    using modificationD(2)[OF assms(2)] by presburger
  then show "AE x in proc_source X. process X t x = process Z t x"
    using XY by fastforce
qed

text_raw \<open>\DefineSnippet{indistinguishable}{\<close>
definition indistinguishable :: "('t,'a,'b) stochastic_process \<Rightarrow> ('t,'a,'b) stochastic_process \<Rightarrow> bool" where
"indistinguishable X Y \<longleftrightarrow> compatible X Y \<and> (\<exists>N \<in> null_sets (proc_source X).
  \<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)"
text_raw \<open>}%EndSnippet\<close>

lemma indistinguishableI:
  assumes "compatible X Y" 
   and "\<exists>N \<in> null_sets (proc_source X). (\<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)"
  shows "indistinguishable X Y"
  unfolding indistinguishable_def using assms by blast

lemma indistinguishable_null_set:
  assumes "indistinguishable X Y"
  obtains N where 
    "N \<in> null_sets (proc_source X)"
    "\<And>t. t \<in> proc_index X \<Longrightarrow> {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N"
  using assms unfolding indistinguishable_def by force

lemma indistinguishableD:
  assumes "indistinguishable X Y"
  shows "compatible X Y"
    and "\<exists>N \<in> null_sets (proc_source X). (\<forall>t \<in> proc_index X. {x \<in> space (proc_source X). X t x \<noteq> Y t x} \<subseteq> N)"
  using assms unfolding indistinguishable_def by blast+

lemma indistinguishable_eq_AE:
  assumes "indistinguishable X Y"
  shows "AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Y t x"
  apply (simp add: eventually_ae_filter)
  using indistinguishableD(2)[OF assms]
  by (smt (verit, del_insts) mem_Collect_eq subset_eq)

lemma indistinguishable_null_ex:
  assumes "indistinguishable X Y"
  shows "\<exists>N \<in> null_sets (proc_source X). {x \<in> space (proc_source X).\<exists>t \<in> proc_index X. X t x \<noteq> Y t x} \<subseteq> N"
  using indistinguishableD(2)[OF assms] by blast

lemma indistinguishable_refl [simp]: "indistinguishable X X"
  by (auto intro: indistinguishableI)

lemma indistinguishable_sym: "indistinguishable X Y \<Longrightarrow> indistinguishable Y X"
  apply (intro indistinguishableI)
  using compatible_sym indistinguishable_def apply blast
  by (smt (verit, ccfv_SIG) Collect_cong compatible_index compatible_source indistinguishable_def)

lemma indistinguishable_trans: 
  assumes "indistinguishable X Y" "indistinguishable Y Z" 
  shows "indistinguishable X Z"
proof (intro indistinguishableI)
  show "compatible X Z"
    using assms indistinguishableD(1) compatible_trans by blast
  have eq: "proc_index X = proc_index Y" "proc_source X = proc_source Y"
    using compatible_index compatible_source indistinguishableD(1)[OF assms(1)] by blast+
  have "AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Y t x"
    by (fact indistinguishable_eq_AE[OF assms(1)])
  moreover have "AE x in proc_source X. \<forall>t \<in> proc_index X. Y t x = Z t x"
    apply (subst eq)+
    by (fact indistinguishable_eq_AE[OF assms(2)])
  ultimately have "AE x in proc_source X. \<forall>t \<in> proc_index X. X t x = Z t x"
    using assms by fastforce
  then obtain N where "N\<in>null_sets (proc_source X)" "{x \<in> space (proc_source X).\<exists>t\<in>proc_index X. process X t x \<noteq> process Z t x} \<subseteq> N"
    using eventually_ae_filter[of]
    by (smt (verit) Collect_cong eventually_ae_filter)
  then show "\<exists>N\<in>null_sets (proc_source X). \<forall>t\<in>proc_index X. {x \<in> space (proc_source X). process X t x \<noteq> process Z t x} \<subseteq> N"
    by blast
qed

text \<open> Klenke 21.5(i) \<close>

text_raw \<open>\DefineSnippet{modification_countable}{\<close>
lemma modification_countable:
  assumes "modification X Y" "countable (proc_index X)"
  shows "indistinguishable X Y"
text_raw \<open>}%EndSnippet\<close>
proof (rule indistinguishableI)
  show "compatible X Y"
    using assms(1) modification_def by auto
  let ?N = "(\<lambda>t. {x \<in> space (proc_source X). X t x \<noteq> Y t x})"
  from assms(1) have "\<forall>t \<in> proc_index X. AE x in proc_source X. X t x = Y t x"
    unfolding modification_def by argo
  then have "\<And>t. t \<in> proc_index X \<Longrightarrow> \<exists>N \<in> null_sets (proc_source X). ?N t \<subseteq> N"
    by (subst eventually_ae_filter[symmetric], blast)
  then have "\<exists>N. \<forall>t \<in> proc_index X. N t \<in> null_sets (proc_source X) \<and> ?N t \<subseteq> N t"
    by meson
  then obtain N where N: "\<forall>t \<in> proc_index X. (N t) \<in> null_sets (proc_source X) \<and> ?N t \<subseteq> N t"
    by blast
  then have null: "(\<Union>t \<in> proc_index X. N t) \<in> null_sets (proc_source X)"
    by (simp add: null_sets_UN' assms(2))
  moreover have "\<forall>t\<in>proc_index X. ?N t \<subseteq> (\<Union>t \<in> proc_index X. N t)"
    using N by blast 
  ultimately show "\<exists>N\<in> null_sets (proc_source X). (\<forall>t\<in>proc_index X. ?N t \<subseteq> N)"
    by blast
qed

(* definition "right_continuous_on s f \<equiv> \<forall>x \<in> s. continuous (at x within {x<..} \<inter> s) f" *)

text \<open> Klenke 21.5(ii). His statement is more general - we reduce right continuity to regular continuity \<close>

text_raw \<open>\DefineSnippet{modification_continuous_indistinguishable}{\<close>
lemma modification_continuous_indistinguishable:
  fixes X :: "(real, 'a, 'b :: metric_space) stochastic_process"
  assumes modification: "modification X Y"
    and interval: "\<exists>T > 0. proc_index X = {0..T}"
      and rc: "AE \<omega> in proc_source X. continuous_on (proc_index X) (\<lambda>t. X t \<omega>)"
                  (is "AE \<omega> in proc_source X. ?cont_X \<omega>")
              "AE \<omega> in proc_source Y. continuous_on (proc_index Y) (\<lambda>t. Y t \<omega>)"
                  (is "AE \<omega> in proc_source Y. ?cont_Y \<omega>")
  shows "indistinguishable X Y"
text_raw \<open>}%EndSnippet\<close>
proof (rule indistinguishableI)
  show "compatible X Y"
    using modification modification_def by blast
  obtain T where T: "proc_index X = {0..T}" "T > 0"
    using interval by blast
  define N where "N \<equiv> \<lambda>t. {x \<in> space (proc_source X). X t x \<noteq> Y t x}"
  have 1: "\<forall>t \<in> proc_index X. \<exists>S. N t \<subseteq> S \<and> S \<in> null_sets (proc_source X)"
    using modificationD(2)[OF modification] by (auto simp add: N_def eventually_ae_filter)
  text \<open> S is a null set such that X t x \<noteq> Y t x ==> x \<in> S t \<close>
  obtain S where S: "\<forall>t \<in> proc_index X. N t \<subseteq> S t \<and> S t \<in> null_sets (proc_source X)"
    using bchoice[OF 1] by blast
  have eq: "proc_source X = proc_source Y" "proc_index X = proc_index Y"
    using \<open>compatible X Y\<close> compatible_source compatible_index by blast+
  have "AE p in proc_source X. ?cont_X p \<and> ?cont_Y p"
    apply (rule AE_conjI)
    using eq rc by argo+
  text \<open> R is a set of measure 1 such that if x \<in> R then the paths at x are continuous for X and Y \<close>
  then obtain R where R: "R \<subseteq> {p \<in> space (proc_source X). ?cont_X p \<and> ?cont_Y p}"
    "R \<in> sets (proc_source X)" "measure (proc_source X) R = 1"
    using proc_source.AE_E_prob by blast
  text \<open> We use an interval of dyadic rationals because we need to produce a countable dense set
  for {0..T}, which we have by @{thm dyadic_interval_dense}. \<close>
  let ?I = "dyadic_interval 0 T"
  let ?N' = "\<Union>n \<in> ?I. N n"
  have N_subset: "\<And>t. t \<in> proc_index X \<Longrightarrow> N t \<inter> R \<subseteq> ?N'"
  proof
    fix t assume "t \<in> proc_index X"
    fix p assume *: "p \<in> N t \<inter> R"
    then obtain \<epsilon> where \<epsilon>: "0 < \<epsilon>" "\<epsilon> = dist (X t p) (Y t p)"
      by (simp add: N_def)
    have cont_p: "continuous_on {0..T} (\<lambda>t. Y t p)" "continuous_on {0..T} (\<lambda>t. X t p)"
      using R *(1) T(1)[symmetric] eq(2) by auto
    then have continuous_dist: "continuous_on {0..T} (\<lambda>t. dist (X t p) (Y t p))"
      using continuous_on_dist by fast
    {
      assume "\<forall>r\<in> ?I. X r p = Y r p"
      then have dist_0: "\<And>r. r \<in> ?I \<Longrightarrow> dist (X r p) (Y r p) = 0"
        by auto
      have "dist (X t p) (Y t p) = 0"
      proof -
        have dist_tendsto_0: "((\<lambda>t. dist (X t p) (Y t p)) \<longlongrightarrow> 0)(at t within ?I)"
          using dist_0 continuous_dist
          by (smt (verit, best) Lim_transform_within \<epsilon> tendsto_const)
        have XY: "((\<lambda>t. X t p) \<longlongrightarrow> X t p)(at t within ?I)" "((\<lambda>t. Y t p) \<longlongrightarrow> Y t p)(at t within ?I)"
          by (metis cont_p T(1) \<open>t \<in> proc_index X\<close> continuous_on_def tendsto_within_subset dyadic_interval_subset_interval)+
        show ?thesis
          apply (rule tendsto_unique[of "at t within ?I"])
          defer
          using tendsto_dist[OF XY] dist_tendsto_0 apply simp
          using tendsto_dist[OF XY] dist_tendsto_0 apply simp
          apply (simp add: trivial_limit_within)
          by (metis T(1) T(2) \<open>t \<in> proc_index X\<close> dyadic_interval_dense islimpt_Icc limpt_of_closure)
      qed
      then have False
        using \<epsilon> by force
    }
    then have "\<exists>r\<in>dyadic_interval 0 T. p \<in> N r"
      unfolding N_def using * R(2) sets.sets_into_space by auto
    then show "p \<in> \<Union> (N ` ?I)"
      by simp
  qed
  thm N_subset
  have null: "(space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. S r) \<in> null_sets (proc_source X)"
    apply (rule null_sets.Un)
     apply (smt (verit) R(2,3) AE_iff_null_sets proc_source.prob_compl proc_source.prob_eq_0 sets.Diff sets.top)
    by (metis (no_types, lifting) S T(1) dyadic_interval_countable dyadic_interval_subset_interval in_mono null_sets_UN')
  have "(\<Union>r \<in> proc_index X. N r) \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> proc_index X. N r)"
    by blast
  also have "... \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. N r)"
    using N_subset N_def by blast
  also have "... \<subseteq> (space (proc_source X) - R) \<union> (\<Union>r \<in> ?I. S r)"
    by (smt (verit, ccfv_threshold)S T(1) UN_iff Un_iff dyadic_interval_subset_interval in_mono subsetI)
  finally show "\<exists>N\<in>null_sets (proc_source X). \<forall>t\<in>proc_index X. {x \<in> space (proc_source X). process X t x \<noteq> process Y t x} \<subseteq> N"
    by (smt (verit) N_def null S SUP_le_iff order_trans)
qed

lift_definition restrict_index :: "('t, 'a, 'b) stochastic_process \<Rightarrow> 't set \<Rightarrow> ('t, 'a, 'b) stochastic_process"
 is "\<lambda>(M, M', I, X) T. (M, M', T, X)" by fast

lemma
  shows
  restrict_index_source[simp]: "proc_source (restrict_index X T) = proc_source X" and
  restrict_index_target[simp]: "proc_target (restrict_index X T) = proc_target X" and
  restrict_index_index[simp]:  "proc_index (restrict_index X T) = T" and
  restrict_index_process[simp]: "process (restrict_index X T) = process X"
  by (transfer, force)+

lemma restrict_index_override[simp]: "restrict_index (restrict_index X T) S = restrict_index X S"
  by (transfer, auto)

lemma compatible_restrict_index:
  assumes "compatible X Y"
  shows "compatible (restrict_index X S) (restrict_index Y S)"
  using assms unfolding compatible_def by auto

lemma modification_restrict_index:
  assumes "modification X Y" "S \<subseteq> proc_index X"
  shows "modification (restrict_index X S) (restrict_index Y S)"
  using assms unfolding modification_def
    apply (auto simp: compatible_restrict_index)
    apply (metis restrict_index_source subsetD)
  done

lemma indistinguishable_restrict_index:
  assumes "indistinguishable X Y" "S \<subseteq> proc_index X"
  shows "indistinguishable (restrict_index X S) (restrict_index Y S)"
  using assms unfolding indistinguishable_def by (auto simp: compatible_restrict_index)

lemma modification_imp_identical_distributions:
  assumes "modification X Y" "T \<subseteq> proc_index X"
  shows "distributions X T = distributions Y T"
  unfolding distributions_altdef
  apply (rule PiM_cong)
   apply simp
  apply (rule distr_cong_AE)
  using assms(1) compatible_source modificationD(1) apply auto[1]
  using assms(1) compatible_target modificationD(1) apply blast
    apply (metis assms modificationD(2) subset_eq)
   apply simp
  using assms(1) modificationD(1) apply simp
  done

end