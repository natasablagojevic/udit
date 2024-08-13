theory Cas4
  imports Main

begin 

lemma "-(A \<union> B) = -A \<inter> -B"
proof
  show "- (A \<union> B) \<subseteq> - A \<inter> - B"
  proof
    fix x 
    assume "x\<in> -(A \<union> B)"
    then have "x \<notin> A \<union> B" by simp
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<in> -A \<and> x \<in> -B" by simp 
    then show "x \<in> -A \<inter> -B" by simp 
  qed

  next 
    show "- A \<inter> - B \<subseteq> - (A \<union> B)"
    proof
      fix x 
      assume "x \<in> -A \<inter> -B" 
      then have "x\<in> -A \<and> x \<in> -B" by simp 
      then have "x \<notin> A \<and> x \<notin> B" by simp 
      then have "x \<notin> A \<union> B" by simp 
      then show "x \<in> - (A \<union> B)" by simp 
    qed
  qed

lemma "A \<union> B = B \<union> A"
proof
  show " A \<union> B \<subseteq> B \<union> A"
  proof
    fix x
    assume "x \<in> A \<union> B"
    then have "x \<in> A \<or> x \<in> B" by simp 
    then have "x \<in> B \<or> x \<in> A" using HOL.disj_commute by simp
    then show "x \<in> B \<union> A" by simp
  qed
next 
  show "B \<union> A \<subseteq> A \<union> B"
  proof
    fix x 
    assume "x \<in> B \<union> A"
    then have "x \<in> B \<or> x \<in> A" by simp 
    then have "x \<in> A \<or> x \<in> B" using HOL.disj_commute by simp 
    then show "x \<in> A \<union> B" by simp
  qed
qed

lemma "A \<union> (B \<inter> C ) = (A \<union> B ) \<inter> (A \<union> C )"
proof
  show "A \<union> (B \<inter> C) \<subseteq> (A \<union> B) \<inter> (A \<union> C)"
  proof
    fix x
    assume "x \<in> A \<union> (B \<inter> C)"
    then have "x \<in> A \<or> x \<in> (B \<inter> C)" by simp 
    then have "x \<in> A \<or> (x \<in> B \<and> x \<in> C)" by simp 
    then have "(x \<in> A \<or> x \<in> B) \<and> (x \<in> A \<or> x \<in> C)" using HOL.disj_conj_distribL by simp 
    then have "x \<in> (A \<union> B) \<and> x \<in> (A \<union> C)" by simp 
    then show "x \<in> (A \<union> B) \<inter> (A \<union> C)" by simp
  qed
next 
  show "(A \<union> B) \<inter> (A \<union> C) \<subseteq> A \<union> (B \<inter> C)"
  proof
    fix x 
    assume "x \<in> (A \<union> B) \<inter> (A \<union> C)" 
    then have "x \<in> (A \<union> B) \<and> x \<in> (A \<union> C)" by simp 
    then have "(x \<in> A \<or> x \<in> B) \<and> (x \<in> A \<or> x \<in> C)" by simp 
    then have "x \<in> A \<or> (x \<in> B \<and> x \<in> C)" using  HOL.disj_conj_distribL by simp
    then have "x \<in> A \<or> x \<in> (B \<inter> C)" by simp 
    then show "x \<in> A \<union> (B \<inter> C)" by simp 
  qed
qed


lemma "A \<inter> (B \<union> C ) = (A \<inter> B ) \<union> (A \<inter> C )"
proof
  show "A \<inter> (B \<union> C) \<subseteq> (A \<inter> B) \<union> (A \<inter> C)"
  proof
    fix x
    assume "x \<in> A \<inter> (B \<union> C)"
    then have "x \<in> A \<and> x \<in> (B \<union> C)" by simp 
    then have "x \<in> A \<and> (x \<in> B \<or> x \<in> C)" by simp 
    then have "(x \<in> A \<and> x \<in> B) \<or> (x \<in> A \<and> x \<in> C)" using HOL.conj_disj_distribL by simp
    then have "x \<in> (A \<inter> B) \<or> x \<in> (A \<inter> C)" by simp 
    then show "x \<in> (A \<inter> B) \<union> (A \<inter> C)" by simp 
    qed
next 
  show "(A \<inter> B) \<union> (A \<inter> C) \<subseteq> A \<inter> (B \<union> C)"
  proof
    fix x 
    assume "x \<in> (A \<inter> B) \<union> (A \<inter> C)"
    then have "x \<in> (A \<inter> B) \<or> x \<in> (A \<inter> C)" by simp 
    then have "(x \<in> A \<and> x \<in> B) \<or> (x \<in> A \<and> x \<in> C)" by simp 
    then have "x \<in> A \<and> (x \<in> B \<or> x \<in> C)" using HOL.conj_disj_distribL by simp
    then have "x \<in> A \<and> x \<in> (B \<union> C)" by simp 
    then show "x \<in> A \<inter> (B \<union> C)" by simp
  qed
qed

lemma "A - (B \<inter> C ) = (A - B ) \<union> (A - C )"
proof
  show "A - (B \<inter> C) \<subseteq> (A - B) \<union> (A - C)"
  proof
    fix x
    assume "x \<in> A - (B \<inter> C)" 
    then have "x \<in> A \<and> x \<notin> (B \<inter> C)" by simp 
    then have "x \<in> A \<and> (x \<notin> B \<or> x \<notin> C)" by simp 
    then have "(x \<in> A \<and> x \<notin> B) \<or> (x \<in> A \<and> x \<notin> C)" by simp 
    then have "x \<in> (A - B) \<or> x \<in> (A - C)" by simp 
    then show "x \<in> (A - B) \<union> (A - C)" by simp 
  qed
next 
  show "(A - B) \<union> (A - C) \<subseteq> A - (B \<inter> C)"
  proof
    fix x 
    assume "x \<in> (A - B) \<union> (A - C)"
    then have "x \<in> (A - B) \<or> x \<in> (A - C)" by simp 
    then have "(x \<in> A \<and> x \<notin> B) \<or> (x \<in> A \<and> x \<notin> C)" by simp 
    then have "x \<in> A \<and> (x \<notin> B \<or> x \<notin> C)" by auto
    then have "x \<in> A \<and> (x \<notin> B \<inter> C)" by simp 
    then show "x \<in> A - (B \<inter> C)" by simp
  qed
qed



end 