theory Wiener_existence
  imports Stochastic_Process
begin
  
thm borel_cantelli_limsup1

text \<open> I am trying to prove the existence of a Wiener process with continuous paths.\<close>

text \<open> The issue is that Kolmogorov's theorem does not guarantee continuity - it merely proves the
  existence of a process with given finite-dimensional distributions. \<close>

text \<open> Our statement of Kolmogorov's theorem is the following \<close>

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

lemma brownian_motion_exists: "\<exists>M X. wiener M W"
proof -

(*theorem (in prob_space) "\<exists>W. wiener M W \<and> (AE \<omega> in M. continuous_on {0..} (\<lambda>t. W t \<omega>))"
proof -
  let ?I = "\<lambda>n k. {k*(1/2^n)..(k+2)*(1/2^n)}"
  define M_nk where "M_nk n k \<omega> = Sup {abs (W r \<omega> - W (k/2^n) \<omega>) | r. r \<in> ?I n k }" for n k \<omega>
  define M_n where "M_n n \<omega> = Max {M_nk n k \<omega> | k. 0 \<le> k \<and> k < n*2^n}" for n \<omega>
  assume *: "(\<Sum>n. \<P>(\<omega> in M. M_n n \<omega> > (1/real n))) \<noteq> \<infinity>"
  let ?B = "limsup (\<lambda>n. M_n n \<omega> > (1/real n))"
  have "prob ?B = 0"
    oops
*)

theorem (in prob_space)
  fixes W
  assumes "wiener M W"
  shows "\<exists>P. (AE \<omega> in P. continuous_on {0..} \<omega>) \<and> (\<forall> J \<subseteq> {0..}. \<forall>X \<in> sets (\<Pi>\<^sub>M i\<in>J. borel). finite J \<longrightarrow> 
  emeasure (stochastic_process.distributions M borel W J) X = P (prod_emb {0..} (\<lambda>_. borel) J X))"
  oops
end