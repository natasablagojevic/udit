theory Funkcije
  imports Main

begin

lemma "f ` f -` f ` A \<subseteq> f ` A"
proof
  fix y 
  assume "y \<in> f ` f -` f ` A"
  then obtain x where "x \<in> f -` f ` A" "f x = y" by auto 
  from this have "f x \<in> f ` A" by auto 
  from this show "y \<in> f ` A" using \<open>f x = y\<close> by auto
qed

lemma 
  shows "f ` (A \<union> B) = f ` A \<union> f ` B"
proof
  show "f ` (A \<union> B) \<subseteq> f ` A \<union> f ` B"
  proof
    fix y
    assume "y \<in> f ` (A \<union> B)"
    then obtain x where "x \<in> A \<union> B" "f x = y" by auto 
    then have "x \<in> A \<or> x \<in> B" by auto 
    then show "y \<in> f ` A \<union> f ` B" 
    proof
      assume "x \<in> A" 
      then have "f x \<in> f ` A" by auto 
      from this have "y \<in> f ` A" using \<open>f x = y\<close> by auto 
      then show "y \<in> f ` A \<union> f ` B" by auto 
    next 
      assume "x \<in> B"
      then have "f x \<in> f ` B" by auto 
      from this have "y \<in> f ` B" using \<open>f x = y\<close> by auto 
      then show "y \<in> f ` A \<union> f ` B" by auto 
    qed
  qed
next 
  show "f ` A \<union> f ` B \<subseteq> f ` (A \<union> B)"
  proof
    fix y 
    assume "y \<in> f ` A \<union> f ` B" 
    then show "y \<in> f ` (A \<union> B)"
    proof
      assume "y \<in> f ` A"
      then obtain x where "x \<in> A" "f x = y" by auto 
      then have "x \<in> A \<union> B" by auto 
      then have "f x \<in> f ` (A \<union> B)" by auto
      with \<open>f x = y\<close> show "y \<in> f ` (A \<union> B)" by auto
    next 
      assume "y \<in> f ` B"
      then obtain x where "x \<in> B" "f x = y" by auto 
      then have "x \<in> A \<union> B" by auto 
      then have "f x \<in> f ` (A \<union> B)" by auto 
      with \<open>f x = y\<close> show "y \<in> f ` (A \<union> B)" by auto
    qed
  qed
qed

lemma 
  assumes "inj f"
  shows "f ` (A \<inter> B) = f ` A \<inter> f ` B"
proof
  show "f ` (A \<inter> B) \<subseteq> f ` A \<inter> f ` B"
  proof
    fix y 
    assume "y \<in> f ` (A \<inter> B)"
    then obtain x where "x \<in> A \<inter> B" "f x = y" by auto 
    then have "x \<in> A \<and> x \<in> B" by auto 
    then have "x \<in> A" "x \<in> B" by auto 
    then have "f x \<in> f ` A" "f x \<in> f ` B" by auto
    then have "y \<in> f ` A" "y \<in> f ` B" using \<open>f x = y\<close> by auto
    then show "y \<in> f ` A \<inter> f ` B" by auto 
  qed
next 
  show "f ` A \<inter> f ` B \<subseteq> f ` (A \<inter> B)"
  proof
    fix y 
    assume "y \<in> f ` A \<inter> f ` B"
    then obtain x1 x2 where "x1 \<in> A" "x2 \<in> B" "f x1 = y" "f x2 = y" by auto 
    from assms have "x1 = x2" using \<open>f x1 = y\<close> \<open>f x2 = y\<close> by (simp add: inj_def)
    then have "x1 \<in> A \<inter> B" using \<open>x1 \<in> A\<close> \<open>x2 \<in> B\<close> by auto 
    then have "y \<in> f ` (A \<inter> B)" using \<open>f x1 = y\<close> by auto 
    then show "y \<in> f ` (A \<inter> B)" by auto 
  qed
qed

lemma 
  assumes "surj f"
  shows "f ` f -` B = B"
proof
  show "f ` f -` B \<subseteq> B"
  proof
    fix y
    assume "y \<in> f ` f -` B"
    then obtain x where "x \<in> f -` B" "f x = y" by auto 
    then have "f x \<in> B" by auto
    then show "y \<in> B" using \<open>f x = y\<close> by auto  
  qed
next 
  show "B \<subseteq> f ` f -` B"
  proof
    fix y
    assume "y \<in> B"
    then obtain x where "f x = y" using surj_def by blast
    then have "x \<in> f -` B" using \<open>y \<in> B\<close> by auto 
    then show "y \<in> f ` f -` B" using \<open>f x = y\<close> by auto 
  qed
qed



end