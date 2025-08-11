
(*<*)
theory Vezbe05
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Svojstva funkcija]\<close>

text \<open>Pokazati da je slika unije, unija pojedinačnih slika.\\
      \<open>Savet\<close>: Razmotriti teoreme \<open>image_def\<close> i \<open>vimage_def\<close>.\<close>

lemma image_union:
  shows "f ` (A \<union> B) = f ` A \<union> f ` B"
proof
  show "f ` (A \<union> B) \<subseteq> f ` A \<union> f ` B"
  proof
    fix y 
    assume "y \<in> f ` (A \<union> B)"
    then obtain x where "x \<in> A \<union> B" "f x = y" by auto 
    then have "x \<in> A \<or> x \<in> B" by auto 
    then have "f x \<in> f ` A \<or> f x \<in> f ` B" by auto 
    then have "y \<in> f ` A \<or> y \<in> f ` B" using \<open>f x = y\<close> by auto 
    then show "y \<in> f ` A \<union> f ` B" by auto
  qed
next 
  show "f ` A \<union> f ` B \<subseteq> f ` (A \<union> B)"
  proof
    fix y
    assume "y \<in> f ` A \<union> f ` B" 
    then have "y \<in> f ` A \<or> y \<in> f ` B" by auto 
    then show "y \<in> f ` (A \<union> B)" 
    proof
      assume "y \<in> f ` A"
      then obtain x where "x \<in> A" "f x = y" by auto 
      then have "x \<in> A \<union> B" by auto 
      then have "f x \<in> f ` (A \<union> B)" by auto
      then show "y \<in> f ` (A \<union> B)" using \<open>f x = y\<close> by auto
    next 
      assume "y \<in> f ` B"
      then obtain x where "x \<in> B" "f x = y" by auto 
      then have "x \<in> A \<union> B" by auto 
      then have "f x \<in> f ` (A \<union> B)" by auto 
      then show "y \<in> f ` (A \<union> B)" using \<open>f x = y\<close> by auto 
    qed
  qed
qed

text \<open>Neka je funkcija \<open>f\<close> injektivna. 
      Pokazati da je slika preseka, presek pojedinačnih slika.\\
      \<open>Savet\<close>: Razmotriti teoremu \<open>inj_def\<close>.\<close>

lemma image_inter: 
  assumes "inj f"
    shows "f ` (A \<inter> B) = f ` A \<inter> f ` B"
proof
  show "f ` (A \<inter> B) \<subseteq> f ` A \<inter> f ` B" 
  proof
    fix y
    assume "y \<in> f ` (A \<inter> B)"
    then obtain x where "x \<in> A \<inter> B" "f x = y" by auto 
    then have "x \<in> A \<and> x \<in> B" by auto 
    then have "f x \<in> f ` A \<and> f x \<in> f ` B" by auto 
    then have "y \<in> f ` A \<and> y \<in> f ` B" using \<open>f x = y\<close> by auto 
    then show "y \<in> f ` A \<inter> f ` B" by auto 
  qed
next 
  show "f ` A \<inter> f ` B \<subseteq> f ` (A \<inter> B)"
  proof
    fix y 
    assume "y \<in> f ` A \<inter> f ` B"
    then have "y \<in> f ` A \<and> y \<in> f ` B" by auto 
    then obtain x1 x2 where "x1 \<in> A" "x2 \<in> B" "f x1 = y" "f x2 = y" by auto 
    then have "x1 = x2" using \<open>f x1 = y\<close> \<open>f x2 = y\<close> using assms  by (simp add: inj_def)
    then have "x1 \<in> A \<inter> B" using \<open>x1 \<in> A\<close> \<open>x2 \<in> B\<close> by auto 
    then have "f x1 \<in> f ` (A \<inter> B)" by auto 
    then show "y \<in> f ` (A \<inter> B)" using \<open>f x1 = y\<close> by auto  
  qed
qed

text \<open>\<open>Savet\<close>: Razmotriti teoremu \<open>surj_def\<close> i \<open>surjD\<close>.\<close>

lemma surj_image_vimage:
  assumes "surj f"
    shows "f ` (f -` B) = B"
proof
  show "f ` f -` B \<subseteq> B"
  proof
    fix y
    assume "y \<in> f ` f -` B"
    then obtain x where "x \<in> f -` B" "f x = y" by auto 
    then have "f x \<in> B" by auto 
    then show "y \<in> B" using \<open>f x = y\<close>  by auto  
  qed
next 
  show "B \<subseteq> f ` f -` B"
  proof
    fix y 
    assume "y \<in> B"
    from assms obtain x where "f x = y" using surj_def by metis
    then have "x \<in> f -` B" using \<open>y \<in> B\<close> by auto 
    then show "y \<in> f ` f -` B" using \<open>f x = y\<close> by auto 
  qed
qed

text \<open>Pokazati da je kompozicija injektivna 
      ako su pojedinačne funkcije injektivne.\\
      \<open>Savet\<close>: Razmotrite teoremu \<open>inj_eq\<close>.\<close>

lemma comp_inj:
  assumes "inj f"
      and "inj g"
    shows "inj (f \<circ> g)"
proof (rule injI)
  fix x y 
  assume "(f \<circ> g) x = (f \<circ> g) y"
  then have "f (g x) = f (g y)" by auto
  then have "g x = g y" using assms(1) by (simp add: inj_def)
  then show "x = y" using assms(2) by (simp add: inj_def)
qed

lemma
  assumes "inj f"
    shows "x \<in> A \<longleftrightarrow> f x \<in> f ` A"
proof
  assume "x \<in> A"
  then show "f x \<in> f ` A" by auto
next 
  assume "f x \<in> f ` A" 
  then obtain y where "y \<in> A" "f x = f y" by auto
  with assms have "x = y" unfolding inj_def by auto 
  then show "x \<in> A" using \<open>y \<in> A\<close> by auto  
qed


lemma inj_vimage_image:
  assumes "inj f"
    shows "f -` (f ` A) = A"
proof
  show "f -` f ` A \<subseteq> A"
  proof
    fix x
    assume "x \<in> f -` f ` A"
    then have "f x \<in> f ` A" by auto 
    then obtain y where "y \<in> A" "f x = f y" by auto 
    with assms have "x = y" unfolding inj_def by auto 
    then show "x \<in> A" using \<open>y \<in> A\<close> by auto  
  qed
next 
  show "A \<subseteq> f -` f ` A"
  proof
    fix x 
    assume "x \<in> A" 
    then have "f x \<in> f ` A" by auto 
    then show "x \<in> f -` f ` A" by auto  
  qed
qed

text \<open>Kompozicija je surjekcija
      ako su pojedinačne funkcije surjekcije.\<close>

lemma comp_surj:
  assumes "surj f"
      and "surj g"
    shows "surj (f \<circ> g)"
proof 
  fix z
  from assms(1) obtain y where "z = f y" by auto 
  moreover
  from assms(2) obtain x where "y = g x" by auto
  ultimately
  have "z = f (g x)" by auto 
  then show "\<exists>x. z = (f \<circ> g) x" by auto 
qed

lemma vimage_compl: 
  shows "f -` (- B) = - (f -` B)"
proof
  show "f -` (-B) \<subseteq> - (f -` B)"
  proof
    fix x 
    assume "x \<in> f -` (-B)" 
    then have "f x \<in> - B" by auto 
    then have "f x \<notin> B" by auto 
    then have "x \<notin> f -` B" by auto 
    then show "x \<in> - (f -` B)" by auto 
  qed
next 
  show "- (f -` B) \<subseteq> f -` (-B)"
  proof
    fix x
    assume "x \<in> - (f -` B)"
    then have "x \<notin> f -` B" by auto 
    then have "f x \<notin> B" by auto 
    then have "f x \<in> - B" by auto 
    then show "x \<in> f -` (-B)" by auto  
  qed
qed

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
