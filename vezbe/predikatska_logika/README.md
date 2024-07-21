# Predikatska Logika

∃, ∀

#### Zadatak 1

```
Svako zadovoljstvo se placa.

z(x) = x je zadovoljstvo 
p(x) = x se placa

---------------------------

(∀x)(z(x) => p(x)) 

```

#### Zadatak 2

```
Postoji zadovoljstvo koje se placa.

z(x) = x je zadovoljstvo
p(x) = x se placa

--------------------

(∃x)(z(x) & p(x))

```

#### Zadatak 3

```
Ni jedno zadovoljstvo nije posao.

z(x) = x je zadovoljstvo 
p(x) = x je posao

---------------------------------

(∀x)(z(x) => ~p(x))

```

#### Zadatak 4

```
Sve sto leti ima krila i lagano je.
Sve sto pliva to nema krila.
Sve sto pliva to ne leti.

l(x) = x leti
ll(x) = x je lagano
p(x) = x pliva
k(x) = x ima krila

--------------------

(∀x)(l(x) => (k(x) & ll(x)))
(∀x)(p(x) => ~k(x))
(∀x)(p(x) => ~l(x))

```

#### Zadatak 5

```
Dve nemimoilazne prave se seku ili su paralelne.
Prave koje se seku leze u istoj ravni.
Prave koje su paralelne leze u istoj ravni.
Dve nemimoilazne prave leze u istoj ravni.

m(x, y) = x i y su nemimoilazne prave
s(x, y) = x i y se seku
p(x, y) = x i y su paralelne
r(x, y) = x i y leze u istoj ravni

---------------------------------------------------

(∀x)(∀y)(m(x, y) => (s(x, y) | p(x, y)))
(∀x)(∀y)(s(x, y) => r(x, y))
(∀x)(∀y)(p(x, y) => r(x, y))
(∀x)(∀y)(m(x, y) => r(x, y))

```

#### Zadatak 6

```
Svaka dva brata imaju zajednickog roditelja.
Roditelj je stariji od deteta.
Postoje braca.
Ni jedna osoba nije starija od druge.

b(x, y) = x i y su braca
r(x, y) = x je roditelj od y
s(x, y) = x je stariji od y

----------------------------------------------

(∀x)(∀y)(∃z)(b(x, y) => (r(z, x) & r(z, y)))
(∀x)(∀y)(r(x, y) => s(x, y))
(∃x)(∃y) b(x, y)
(∀x)(∀y) ~s(x, y)

```

#### Zadatak 7

```
Svako ima rodjaka na moru ili na planini.
Ko ima rodjaka na moru, bio je na moru.
Ko ima rodjaka na planini, bio je na planini.
Niko nije bio ni na moru, ni na planini.

rm(x) = x ima rodjaka na moru
rp(x) = x ima rodjaka na planini
m(x) = x je bio na moru
p(x) = x je bio na planini

----------------------------------------------

(∀x)(rm(x) | rp(x))
(∀x)(rm(x) => m(x))
(∀x)(rp(x) => p(x))
(∃x)(~m(x) & ~p(x))

```

#### Zadatak 8

```
Svako ruca kod kuce ili u restoranu.
Ko ruca u restoranu i nema novca, taj pere sudove u restoranu.
Janko nema novca.
Janko ruca kod kuce ili pere sudove u restoranu.

rk(x) = x ruca kod kuce
rr(x) = x ruca u restoranu
nn(x) = x nema novca 
ps(x) = x pere sudove

j = Janko

-----------------------------------------------------------------

(∀x)(rk(x) | rr(x))
(∀x)((rr(x) & nn(x)) => ps(x))
nn(j)
rk(j) | ps(j)

```
