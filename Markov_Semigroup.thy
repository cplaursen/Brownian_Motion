theory Markov_Semigroup
  imports Kernel_Composition
begin

text \<open> Klenke definition 14.42 \<close>

locale consistent_family =
  fixes I :: "real set"
    and M :: "'a measure"
    and K :: "real \<Rightarrow> real \<Rightarrow> 'a hkernel"
  assumes "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i < j\<rbrakk> \<Longrightarrow> hkernel_space (K i j) = M"
    and "\<And>i j k. \<lbrakk>i \<in> I; j \<in> I; k \<in> I; i < j; j < k\<rbrakk> \<Longrightarrow> K i j \<circ>\<^sub>K K j k = K i k"
    and "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; i < j\<rbrakk> \<Longrightarrow> stochastic_kernel (K i j)"

text \<open> Klenke definition 14.43 \<close>

(* Klenke specifies that K can range over an additive semigroup, but this
  precludes the below lemma 14.44 where he subtracts elements from the semigroup *)

locale markov_semigroup =
  fixes K :: "real \<Rightarrow> 'a :: polish_space hkernel"
    and M :: "'a measure"
  assumes space_eq_M: "\<And>i. i \<ge> 0 \<Longrightarrow> hkernel_space (K i) = M"
      and init: "\<And>\<omega>. \<omega> \<in> space (kernel_source (K 0))
   \<Longrightarrow> kernel_measure (K 0) \<omega> = return (kernel_source (K 0)) \<omega>"
      and comp_sum: "\<And>s t. \<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> K s \<circ>\<^sub>K K t = K (s + t)"
      and stochastic: "\<And>i. i \<ge> 0 \<Longrightarrow> stochastic_kernel (K i)"

context markov_semigroup begin

lemma kernel_comp_commute: "\<lbrakk>s \<ge> 0; t \<ge> 0\<rbrakk> \<Longrightarrow> K s \<circ>\<^sub>K K t = K t \<circ>\<^sub>K K s"
  by (simp add: add.commute comp_sum)

text \<open> Klenke lemma 14.44 \<close>
lemma (in markov_semigroup) consistent: "consistent_family {0..} M (\<lambda>x y. K (y-x))"
  apply (intro consistent_family.intro)
  apply (rule space_eq_M)
    apply (simp_all add: comp_sum space_eq_M stochastic)
  done

end
end