theory Continuous_Modification
  imports Stochastic_Process Holder_Continuous
begin

text \<open> Klenke 21.6 - Kolmorogov-Chentsov\<close>

theorem holder_continuous_modification:
  fixes X :: "(real, 'a, real) stochastic_process"
  assumes index: "proc_index X = {0..}"
      and gt_0: "a > 0" "b > 0" "C > 0"
      and "\<And>T s t. \<lbrakk>T > 0; s \<in> {0..T}; t \<in> {0..T}\<rbrakk> \<Longrightarrow> 
          prob_space.expectation (proc_source X) (\<lambda>x. (X t x - X s x) powr a) \<le> C * (dist t s) powr (1+b)"
    shows "\<exists>Y. modification X Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}. AE x in proc_source Y. local_holder_on \<gamma> {0..} (\<lambda>t. Y t x))"
proof -
  text \<open> Quoting Klenke: It is enough to show that for any T > 0 the process X on [0,T] has a
  modification X^T that is locally H{\"o}lder-continuous of any order \<gamma> \<in> (0, b/a).
  For S, T > 0, by lemma 21.5, two such modifications X^S and X^T are indistinguishable on
  [0, min S T], hence
  \[\<Omega>_{S, T} := {\<omega>. \<exists>t \<in> {0..min S T}. X^T t \<omega> \<noteq> X^S t \<omega>}\]
  is a null set and thus also \<Omega>_\<infinity> := \<Union>s \<in> (\<nat> \<times> \<nat>). \<Omega> s is a null set. Therefore, definining
  \tilde{X}_t(\<omega>) := X_t^t(\<omega>), t \<ge> 0, for \<omega> \<in> \<Omega> \ \<Omega>_\<infinity>, we get that \tilde{X} is the process
  we are looking for \<close>
  {
    assume *: "\<And>T. T > 0 \<Longrightarrow> \<exists>Y. modification (restrict_index X {0..T}) Y \<and> (\<forall>\<gamma>\<in>{0<..<(b / a)}.
               AE x in proc_source Y. local_holder_on \<gamma> {0..T} (\<lambda>t. Y t x))"
    fix S T ::real assume ST: "S > 0" "T > 0"
    obtain P where P: "modification (restrict_index X {0..S}) P" "(\<forall>\<gamma>\<in>{0<..<(b / a)}.
               AE x in proc_source P. local_holder_on \<gamma> {0..S} (\<lambda>t. P t x))"
      using *[OF ST(1)] by blast
    obtain Q where Q: "modification (restrict_index X {0..T}) Q" "(\<forall>\<gamma>\<in>{0<..<(b / a)}.
               AE x in proc_source Q. local_holder_on \<gamma> {0..T} (\<lambda>t. Q t x))"
      using *[OF ST(2)] by blast
    have mod_restrict: "modification (restrict_index P {0..min S T}) (restrict_index Q {0..min S T})"
    proof -
      have "modification (restrict_index X {0..min S T}) (restrict_index P {0..min S T})"
        using P(1) restrict_index_override modification_restrict_index by fastforce
      moreover have "modification (restrict_index X {0..min S T}) (restrict_index Q {0..min S T})"
        using Q(1) restrict_index_override modification_restrict_index by fastforce
      ultimately show ?thesis
        using modification_sym modification_trans by blast
    qed
    then have "indistinguishable (restrict_index P {0..min S T}) (restrict_index Q {0..min S T})"
    proof -
      have "b / a > 0"
        using gt_0 by auto
      then obtain \<gamma> where \<gamma>: "\<gamma> \<in> {0<..<(b / a)}" "\<gamma> \<le> 1"
        by (simp, meson field_lbound_gt_zero less_eq_real_def less_numeral_extra(1))
      then have "AE x in proc_source P. continuous_on {0..S} (\<lambda>t. P t x)"
        using P(2) local_holder_continuous by fast
      then have 1: "AE x in proc_source (restrict_index P {0..min S T}). continuous_on {0..min S T} (\<lambda>t. P t x)"
        apply (subst restrict_index_source)
        using continuous_on_subset by fastforce
      have "AE x in proc_source Q. continuous_on {0..T} (\<lambda>t. Q t x)"
        using Q(2) \<gamma> local_holder_continuous by fast
      then have 2: "AE x in proc_source (restrict_index Q {0..min S T}). continuous_on {0..min S T} (\<lambda>t. Q t x)"
        apply (subst restrict_index_source)
        using continuous_on_subset by fastforce
      show ?thesis
        apply (rule modification_continuous_indistinguishable)
           apply (fact mod_restrict)
        using ST(1) ST(2) apply force
        using 1 apply fastforce
        using 2 apply fastforce
        done
    qed
    then obtain N where "{\<omega>. \<exists>t \<in> {0..min S T}. P t \<omega> \<noteq> Q t \<omega>} \<subseteq> N \<and> N \<in> null_sets (proc_source P)"
      unfolding indistinguishable_def apply auto
      sorry
        text \<open> WITHOUT LOSS OF GENERALITY T = 1. (What?)\<close>
end