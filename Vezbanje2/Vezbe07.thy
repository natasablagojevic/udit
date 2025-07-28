
(*<*)
theory Vezbe07
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Alternirajuća suma neparnih prirodnih brojeva]\<close>

text \<open>Pokazati da važi:\<close>

text_raw \<open>$$ - 1 + 3 - 5 + \ldots + (- 1)^n (2n - 1) = (- 1)^n n.$$\<close>

text \<open>Primitivnom rekurzijom definisati funkciju \<open>alternirajuca_suma :: "nat \<Rightarrow> int"\<close> 
      koja računa alternirajucu sumu neparnih brojeva od \<open>1\<close> do \<open>2n - 1\<close>, 
      tj. definisati funkciju koja računa levu stranu jednakosti.\<close>

primrec alternirajuca_suma :: "nat \<Rightarrow> int" where
  "alternirajuca_suma 0 = undefined"
| "alternirajuca_suma (Suc n) = undefined"

primrec suma:: "nat \<Rightarrow> int"
  where "suma 0 = 0"
  | "suma (Suc n) = suma n + (-1)^(Suc n) * (2 * int(Suc n) - 1)"

text \<open>Proveriti vrednost funkcije \<open>alternirajuca_suma\<close> za proizvoljan prirodni broj.\<close>

value "suma 3"

text \<open>Dokazati sledeću lemu induckijom koristeći metode za automatsko dokazivanje.\<close>

lemma "alternirajuca_suma n = (-1)^n * int n"
(*<*) oops (*>*)

lemma "suma n = (-1)^n * int n"
  by (induction n) (auto simp add: algebra_simps)

text \<open>Dokazati sledeću lemu indukcijom raspisivanjem detaljnog Isar dokaza.\<close>

lemma "suma n = (-1)^n * int n"
proof (induction n)
  case 0
  then show ?case by (auto simp add: algebra_simps)
next
  case (Suc n)
  note IH = this
  have "suma (Suc n) = suma n + (-1)^(Suc n) * (2 * int(Suc n) - 1)" by (auto simp add: algebra_simps)
  also have "... = (-1)^n * int n + (-1)^(Suc n) * (2 * int (Suc n) - 1)" using IH by (auto simp add: algebra_simps)
  also have "... = (-1)^n * int n + (-1)^(n+1) * (2 * int(n+1) - 1)" by (auto simp add: algebra_simps)
  also have "... = (-1)^n * int n + (-1)^(n+1) * (2 * int n + 2 - 1)" by (auto simp add: algebra_simps)
  also have "... = (-1)^n * int n + (-1)^(n+1) * (2 * int n + 1)" by (auto simp add: algebra_simps)
  also have "... = (-1)^n * int n - (-1)^n * (2 * int n + 1)" by (auto simp add: algebra_simps)
  also have "... = (-1)^n * int n - (-1)^n * 2 * int n - (-1)^n" by (auto simp add: algebra_simps)
  also have "... = (-1)*(-1)^n * int n - (-1)^n" by (auto simp add: algebra_simps)
  also have "... = (-1)^(n+1) * int n + (-1)^(n+1)" by (auto simp add: algebra_simps)
  also have "... = (-1)^(n+1) * (int n + 1)" by (auto simp add: algebra_simps)
  also have "... = (-1)^(Suc n) * int(Suc n)" by (auto simp add: algebra_simps)
  finally show ?case .
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Množenje matrica]\<close>

text \<open>Pokazati da važi sledeća jednakost:\<close>

text_raw 
\<open>$$
\begin{pmatrix}
1 & 1\\
0 & 1
\end{pmatrix}^n
=
\begin{pmatrix}
1 & n\\
0 & 1
\end{pmatrix},
n \in \mathbb{N}.
$$\<close>

text \<open>Definisati tip \<open>mat2\<close> koji predstavlja jednu \<open>2\<times>2\<close> matricu prirodnih brojeva.
      Tip \<open>mat2\<close> definisati kao skraćenicu uređene četvorke prirodnih brojeva.
      Uređena četvorka odgovara \<open>2\<times>2\<close> matrici kao\<close>

type_synonym mat2 = "nat \<times> nat \<times> nat \<times> nat"

text_raw 
\<open>$$
(a, b, c, d) \equiv
\begin{pmatrix}
a & b\\
c & d
\end{pmatrix}.
$$\<close>

text \<open>Definisati konstantu \<open>eye :: mat2\<close>, koja predstavlja jediničnu matricu.\<close>

definition eye:: "mat2" where "eye = (1,0,0,1)"

text \<open>Definisati funkciju \<open>mat_mul :: mat2 \<Rightarrow> mat2 \<Rightarrow> mat2\<close>, koja množi dve matrice.\<close>

fun mat_mul:: "mat2 \<Rightarrow> mat2 \<Rightarrow> mat2" where
  "mat_mul (a1, b1, c1, d1) (a2, b2, c2, d2) = (a1*a2+b1*c2, a1*b2+b1*d2, c1*a2+d1*c2, c1*b2+d1*d2)"

text \<open>Definisati funkciju \<open>mat_pow :: mat2 \<Rightarrow> nat \<Rightarrow> mat2\<close>, koja stepenuje matricu.\<close>

fun mat_pow:: "mat2 \<Rightarrow> nat \<Rightarrow> mat2" 
  where "mat_pow M 0 = (1,0,0,1)"
  | "mat_pow M (Suc n) = mat_mul (mat_pow M n) M"

text \<open>Dokazati sledeću lemu koristeći metode za automatsko dokazivanje.\<close>

lemma "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
  by (induction n) (auto simp add: algebra_simps)

text \<open>Dokazati sledeću lemu indukcijom raspisivanjem detaljnog Isar dokaza.\<close>

lemma "mat_pow (1, 1, 0, 1) n = (1, n, 0, 1)"
proof (induction n)
  case 0
  then show ?case by (auto simp add: algebra_simps)
next
  case (Suc n)
  note IH = this 
  have "mat_pow (1,1,0,1) (Suc n) = mat_mul (mat_pow (1,1,0,1) n) (1,1,0,1)" by (auto simp add: algebra_simps)
  also have "... = mat_mul (1,n,0,1) (1,1,0,1)" using IH by (auto simp add: algebra_simps)
  also have "... = (1,n+1,0,1)" by (auto simp add: algebra_simps)
  also have "... = (1, Suc n, 0, 1)" by (auto simp add: algebra_simps)
  finally show ?case .
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Deljivost]\<close>

text \<open>Pokazati sledeću lemu.\\
      \<open>Savet\<close>: Obrisati \<open>One_nat_def\<close> i \<open>algebra_simps\<close> iz \<open>simp\<close>-a u 
      finalnom koraku dokaza.\<close>

lemma 
  fixes n::nat
  shows "(6::nat) dvd n * (n + 1) * (2 * n + 1)"
proof (induction n)
  case 0
  then show ?case by (auto simp add: algebra_simps)
next
  case (Suc n)
  then obtain k::nat where IH: "n*(n+1)*(2*n+1) = 6*k" by (auto simp add: algebra_simps)
  have "(Suc n) * (Suc n + 1) * (2 * (Suc n) + 1) = (n+1) * (n+1+1) * (2 * (n+1) + 1)" by (auto simp add: algebra_simps)
  also have "... = (n+1)*(n+2)*(2*n + 2 + 1)" by (auto simp add: algebra_simps)
  also have "... = (n+1)*(n+2)*(2*n+3)" by (auto simp add: algebra_simps)
  also have "... = n*(n+1)*(2*n+3) + 2*(n+1)*(2*n+3)" by (auto simp add: algebra_simps)
  also have "... = n*(n+1)*(2*n+1 + 2) + 2*(n+1)*(2*n+3)" by (auto simp add: algebra_simps)
  also have "... = n*(n+1)*(2*n+1) + 2*n*(n+1) + 2*(n+1)*(2*n+3)" by (auto simp add: algebra_simps)
  also have "... = 6*k + 2*(n+1)*(n + 2*n+3)" using IH  by (auto simp add: algebra_simps)
  also have "... = 6*k + 2*(n+1)*(3*n+3)" by (auto simp add: algebra_simps)
  also have "... = 6*k + 2*3*(n+1)*(n+1)" by (auto simp add: algebra_simps)
  also have "... = 6*k + 6*(n+1)*(n+1)" by (auto simp add: algebra_simps)
  also have "... = 6*k + 6*(Suc n)*(Suc n)" by (auto simp add: algebra_simps)
  finally show ?case using dvdI by blast
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Nejednakost]\<close>

text \<open>Pokazati da za svaki prirodan broj \<open>n > 2\<close> važi \<open>n\<^sup>2 > 2 * n + 1\<close>.\\
     \<open>Savet\<close>: Iskoristiti \<open>nat_induct_at_least\<close> kao pravilo indukcije i 
              lemu \<open>power2_eq_square\<close>.\<close>

thm nat_induct_at_least
thm power2_eq_square

lemma n2_2n:
  fixes n::nat
  assumes "n \<ge> 3"
  shows "n\<^sup>2 > 2 * n + 1"
  using assms
(*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>


(*

1 + 2 + 3 + ... + n = n*(n+1)/2

*)

primrec suman:: "nat \<Rightarrow> nat" 
  where "suman 0 = 0"
  | "suman (Suc n) = (Suc n) + suman n"

value "suman 4"

lemma "suman n = (n * (n+1)) div 2"
proof (induction n)
  case 0
  then show ?case by auto 
next
  case (Suc n)
  note IH = this
  have "suman (Suc n) = Suc n + suman n" by (auto simp add: algebra_simps)
  also have "... = Suc n + n * (n + 1) div 2" using IH by (auto simp add: algebra_simps)
  also have "... = (n + 1) + n * (n + 1) div 2" by (auto simp add: algebra_simps)
  also have "... = 2 * (n + 1) div 2 + n * (n + 1) div 2" by (auto simp add: algebra_simps)
  also have "... = (2 * (n+1) + n * (n + 1)) div 2" by (auto simp add: algebra_simps)
  also have "... = (n + 1) * (2 + n) div 2" by (auto simp add: algebra_simps)
  also have "... = Suc n * (Suc n + 1) div 2" by (auto simp add: algebra_simps)
  finally show ?case .
qed




(*<*)
end
(*>*)
