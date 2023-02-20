theory Continuous_Modification
  imports Stochastic_Process Holder_Continuous
begin

definition restrict_index :: "('t, 'a, 'b) stochastic_process \<Rightarrow> 't set \<Rightarrow> ('t, 'a, 'b) stochastic_process"
  where "restrict_index X T \<equiv> process_of (proc_source X) (proc_target X) T (process X)"

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
    obtain Q where Q: "modification (restrict_index X {0..S}) Q" "(\<forall>\<gamma>\<in>{0<..<(b / a)}.
               AE x in proc_source Q. local_holder_on \<gamma> {0..S} (\<lambda>t. Q t x))"
      using *[OF ST(1)] by blast
    oops
    text \<open> WITHOUT LOSS OF GENERALITY T = 1. (What?)\<close>
end