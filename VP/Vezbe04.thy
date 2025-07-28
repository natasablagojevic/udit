
(*<*)
theory Vezbe04
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Algebra skupova]\<close>

text \<open>Diskutovati o sledećim termovima:\<close>

term "{1, 2, 3}"
term "{1::nat, 2, 3}"
term "(\<in>)"
term "(\<inter>)"
term "(\<union>) A"
term "(A::'a set) - B"

text_raw \<open> \end{exercise} \<close>


text_raw \<open>\begin{exercise}[subtitle=Isar dokazi]\<close>

text \<open>Pokazati sledeća tvrđenja o skupovima pomoću jezika Isar.\<close>

text \<open>\<open>Napomena\<close>: Dozvoljeno je korišćenje samo \<open>simp\<close> metode za
                  dokazivanje pojedinačnih koraka.\<close>

lemma "- (A \<union> B) = - A \<inter> - B"
proof
  show "- (A \<union> B) \<subseteq> - A \<inter> - B"
  proof
    fix x
    assume "x \<in> - (A \<union> B)"
    then have "x \<notin> (A \<union> B) " by simp 
    then have "x \<notin> A \<and> x \<notin> B" by simp
    then have "x \<in> -A \<and> x \<in> -B" by simp
    then show "x \<in> -A \<inter> -B" by simp
  qed
next 
  show "- A \<inter> - B \<subseteq> - (A \<union> B)"
  proof
    fix x
    assume "x \<in> -A \<inter> -B"
    then have "x \<in> -A \<and> x \<in> -B" by simp 
    then have "x \<notin> A \<and> x \<notin> B" by simp 
    then have "x \<notin> A \<union> B" by simp
    then show "x \<in> -(A \<union> B)" by simp
  qed
qed

text \<open>\<open>Savet\<close>: Iskoristiti @{text "find_theorems _ \<or> _ \<longleftrightarrow> _ \<or> _"} 
               za pronalaženje odgovarajuće teoreme.\<close>

lemma "A \<union> B = B \<union> A"
proof
  show "A \<union> B \<subseteq> B \<union> A"
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

text \<open>\<open>Savet\<close>: Iskoristiti aksiomu isključenja trećeg @{text "A \<or> \<not>A"}
               u kontekstu operacije pripadanja @{text "(\<in>) :: 'a \<Rightarrow> 'a set \<Rightarrow> bool"}.\<close>

lemma "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)" (is "?left = ?right")
proof
  show "?left \<subseteq> ?right"
  proof
    fix x
    assume "x \<in> A \<union> (B \<inter> C)"
    then have "x \<in> A \<or> x \<in> B \<inter> C" by simp 
    then have "x \<in> A \<or> (x \<in> B \<and> x \<in> C)" by simp 
    then have "(x \<in> A \<or> x \<in> B) \<and> (x \<in> A \<or> x \<in> C)" using HOL.disj_conj_distribL by simp
    then have "x \<in> (A \<union> B) \<and> x \<in> (A \<union> C)" by simp 
    then show "x \<in> (A \<union> B) \<inter> (A \<union> C)" by simp
  qed
next
  show "?right \<subseteq> ?left"
  proof
    fix x
    assume "x \<in> (A \<union> B) \<inter> (A \<union> C)"
    then have "x \<in> (A \<union> B) \<and> x \<in> (A \<union> C)" by simp
    then have "(x \<in> A \<or> x \<in> B) \<and> (x \<in> A \<or> x \<in> C)" by simp 
    then have "x \<in> A \<or> (x \<in> B \<and> x \<in> C)" using disj_conj_distribL by simp
    then have "x \<in> A \<or> x \<in> (B \<inter> C)" by simp 
    then show "x \<in> A \<union> (B \<inter> C)" by simp
  qed
qed

lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" (is "?left = ?right")
proof

qed

lemma "A - (B \<inter> C ) = (A - B) \<union> (A - C )" (is "?left = ?right")
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
