#import "@local/chuletario:1.0.0": conf

#import "@preview/theorion:0.4.0": *
#import cosmos.rainbow: *
#show: show-theorion

// 1. Change the counters and numbering:
#set-inherited-levels(1)
#set-zero-fill(true)
#set-leading-zero(true)
#set-theorion-numbering("1.1")

// 2. Other options:
// #set-result("noanswer") // Deletes the demos.
// #set-qed-symbol[#math.qed] // Changes qed symbol for proofs.

// Makes corollary numbering same as the rest of objects.
#let (corollary-counter, corollary-box, corollary, show-corollary) = make-frame(
  "corollary",
  theorion-i18n-map.at("corollary"),
  counter: theorem-counter,
  render: render-fn.with(fill: fuchsia.darken(10%)),
)

#show: conf.with(
  title: "Chuletario Álgebra II",
  author: "Álvaro Grande Blázquez",
  course: "2025 ~ 2026",
  watermark: "AGB",
)

#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

= Repaso de teoría de cuerpos
== Estructuras algebraicas

#definition(title: "Operación binaria")[
  Sea $C$ un conjunto. Una *operación binaria* en $C$ es una aplicación:

  $ ast: & C times C & -> & thick med C \ & thick (a, b) &|-> & a*b $

  Además, se impone que al operar dos elementos de $C$, el resultado debe estar en $C$.
]

#definition(title: "Grupo")[
  Un *grupo* $(G, ast)$ es un conjunto con una operación binaria $ast$ tal que:
  
  - $ast$ es asociativa: $forall a, b, c in G, thick (a ast b) ast c = a ast (b ast c)$
  - Existe elemento neutro: $exists e in G | forall a in G, thick e ast a = a ast e = a$
  - Existe elemento inverso: $forall a in G thick exists a^(-1) in G | a ast a^(-1) = a^(-1) ast a = e$

El grupo es *conmutativo (abeliano)* si $forall a, b in G, thick a ast b = b ast a$.
]

#definition(title: "Anillo")[
  Un *anillo* $(A, ast, circle.stroked.tiny)$ es un conjunto $A$ con dos operaciones binarias $ast, circle.stroked.tiny$ tales que:

  - $(A, ast)$ es un grupo abeliano.
  - $circle.stroked.tiny$ es asociativa.
  - Se cumplen las leyes de distributividad:
    - $(a ast b) circle.stroked.tiny c = (a circle.stroked.tiny c) ast (b circle.stroked.tiny c)$
    - $a circle.stroked.tiny (b ast c) = (a circle.stroked.tiny b) ast (a circle.stroked.tiny c)$

  El anillo es *conmutativo* si $circle.stroked.tiny$ es conmutativa. \
  El anillo *tiene unidad* si existe un neutro para $circle.stroked.tiny$
]

#note-box[
  En este curso, "anillo" significará anillo conmutativo con unidad (salvo pocas excepciones)
]

#definition(title: "Cuerpo")[
  Un *cuerpo* $(K, ast, circle.stroked.tiny)$ es un conjunto $K$ con al menos dos elementos y dos operaciones binarias $ast, circle.stroked.tiny$ tales que:
  
  - $(K, ast, circle.stroked.tiny)$ es un anillo conmutativo con unidad.
  - Todo elemento $a in K$, $a != e$, tiene un inverso para $circle.stroked.tiny$.
]

#definition[
  Sea $(A, +, ·)$ un anillo. Entonces:

  - Un elemento $a in A$ es un *divisor de cero* si $a != 0$ y existe $b in A without {0}$ tal que $a · b = 0$.
  - Un elemento $a in A$ es una *unidad* si existe $b in A$ tal que $a · b = 1$. Decimos que $b = a^(-1)$ es su inverso.
  - El anillo $A$ es un *dominio de integridad* si $forall a, b in A, thick a · b = 0 => a = 0 or b = 0$, es decir, no hay divisores de 0.
]

#lemma[
  Todo cuerpo es un dominio de integridad.
]

#definition(title: "Anillo de polinomios")[
  Sea $A$ un anillo conmutativo.
  El *anillo de polinomios* $A[X]$ en una variable $x$ es el conjunto de expresiones de la forma:
  $ a_n x^n + a_(n-1) x^(n-1) + ... a_1 x + a_0, quad a_i in A $

  con la suma y el producto habituales.
]

#definition(title: "Grado de un polinomio")[
  Si $P = a_n x^n + ... + a_0 in A[X] "con" a_n != 0$ decimos que $P$ tiene *grado $n$* y ponemos $deg(P) = n$. Si $P = 0$, entonces $deg(P) = -oo$.
]

#proposition[
  Sea $A$ un dominio de integridad. Entonces:

  - $deg(P + Q) <= max{deg(P), deg(Q)}$
  - $deg(P Q) = deg(P) + deg(Q)$
  - $A[X]$ es un dominio de integridad.
]

#definition(title: "Polinomio mónico")[
  Un polinomio $a_n x^n + ... + a_0$ de grado $n>=1$ es *mónico* si $a_n = 1$.
]

#definition(title: "Morfismo de anillos")[
  Sean $A, B$ anillos. Un *(homo)morfismo de anillos* es una aplicación $phi.alt: A -> B$ tal que:

  - $phi.alt(a_1 + a_2) = phi.alt(a_1) + phi.alt(a_2)$
  - $phi.alt(a_1 a_2) = phi.alt(a_1) phi.alt(a_2)$
  - $phi.alt(1_A) = 1_B$
]

#definition[
  - Un morfismo biyectivo de anillos $phi.alt: A -> B$ es un *isomorfismo*.
  - Un morfismo de anillos $phi.alt: A -> A$ es un *endomorfismo*.
  - Un de anillos $phi.alt: A -> A$ que es un isomorfismo se llama *automorfismo*.
]

#definition[
  Sea $phi.alt: A -> B$ un morfismo de anillos:

  - Su *núcleo* es $ker(phi.alt) = {a in A | phi.alt(a) = 0}$.
  - Su *imagen* es $"Im"(phi.alt) = {b in B | phi.alt^(-1)(b) != 0}$
]

#lemma(breakable: false)[
  Sea $phi.alt: A -> B$ un morfismo de anillos:

  - $ker(phi.alt)$ es un subanillo de $A$.
  - $"Im"(phi.alt)$ es un subanillo de $B$.
]

#definition(title: "Morfismo de evaluación")[
  Sean $A subset B$ anillos. Dado $b in B$, la aplicación:

  $ phi.alt_b: A[X] ->B "tal que" (a_n x^n + ... + a_1 x + a_0) |-> (a_n b^n + ... + a_1 b + a_0) $

  es un morfismo de anillos, llamado el *morfismo de evaluación* en $b$.
]

== Ideales y cocientes

#definition(title: "Ideal")[
  Sea $(A, +, ·)$ un anillo. Se dice que $I subset A$ es un *ideal* si:

  - $0 in I$
  - $forall a, b in I, thick a + b in I$
  - $forall a in A, thick forall b in I; thick a · b in I$

  Es decir, $(I, +)$ es un subgrupo e $I$ es absorbente para el producto.
]

#definition[
  Sean $A$ un anillo; $a_1, ..., a_n in A$. El ideal generado por $a_1, ..., a_n$ es el menor ideal que contiene a $a_1, ..., a_n$. Es decir:

  $ angle.l a_1, ..., a_n angle.r = {lambda_1 a_1 + ... + lambda_n a_n | lambda_j in A} $

  Los elementos $a_1, ..., a_n$ se llaman *generadores* del ideal.
]

#definition[
  Sea $A$ un anillo. Un ideal $I subset A$ es:

  - *Principal* si existe $a in A$ tal que $I = angle.l a angle.r $.
  - *Maximal* si $I != A$ y no existe ningún ideal $J subset.not.eq A$ tal que $I subset.not.eq J subset.not.eq A$.
  - *Primo* si $I != A$ y, para todos $x, y in I$, si $x y in I$ entonces o bien $x in I$ o $y in I$.
] 

#proposition[
  Sean $a, b in ZZ$. Supongamos que $a!=0$ o $b!=0$. Entonces:
  $ angle.l a, b angle.r = angle.l m c d(a, b) angle.r $
]

#lemma[
  En $ZZ$:
  - Los *ideales maximales* son ${angle.l p angle.r | p in ZZ "primo"}$.
  - Los *ideales primos* son ${angle.l 0 angle.r} union {angle.l p angle.r | p in ZZ "primo"}$.
]

#definition(title: "Anillo cociente")[
  Sean $A$ un anillo, $I$ un ideal de $A$. Este induce una relación de equivalencia sobre $A$ dada por:

  $ a ~ b <=> a - b in I, thick thick "donde" ~ "es reflexiva, simétrica y transitiva." $

  Esto permite definit el *conjunto cociente* $A slash I$ (el conjunto de clases de equivalencia).
]

#proposition[
  Sean $A$ un anillo, $I subset A$ un ideal. El conjunto cociente $A slash I$ tiene estructura de anillo con las propiedades inducidas por las de $A$:
  $ forall a, b in A, quad overline(a) + overline(b) = overline(a + b) quad y quad overline(a) · overline(b) = overline(a b) $
]

#proposition[
  Sean $A$ un anillo, $I subset A$ un ideal. Entonces:

  - El ideal $I$ es *maximal* si y solo si $A slash I$ es un *cuerpo*.
  - El ideal $I$ es *primo* si y solo si $A slash I$ es un *dominio de integridad*.
]

#corollary[
  Todo ideal maximal es primo.
]

#theorem(title: "Primer Teorema de Isomorfía")[
  Sean $A, B$ dos anillos y $phi.alt: A -> B$ un morfismo de anillos. Entonces:

  - $ker(phi.alt)$ es un ideal de $A$.
  - Existe un isomorfismo $overline(phi.alt): A slash ker(phi.alt) -> "Im"(phi.alt)$ tal que el siguiente diagrama conmuta:

  #align(center,
    diagram(cell-size: 15mm, $
	  A edge(phi.alt, ->) edge("d", pi, ->>) & "Im"(phi.alt) \
	  A slash ker(phi.alt) edge("ur", overline(phi.alt), "hook-->")
  $)
  )

  Decimos que $phi.alt$ factoriza a través de $pi$.
]

== Factorización en anillos de polinomios

#theorem(title: "Teorema Fundamental de la Aritmética")[
  Todo entero mayor que $1$ puede expresarse de forma única como un producto de números primos, salvo reordenación de los factores.
]

#definition[
  Sea $A$ un dominio de integridad.
  Un elemento $a in A without {0}$ es *irreducible* si no es una unidad y, para todos $b, c in A, thick a = b c$ implica que $b$ o $c$ son unidades.
]

#definition(title: "Dominio de factorización única (DFU)")[
  Sea $A$ un dominio de integridad.
  Se dice que $A$ es un *dominio de factorización única (DFU)* si todo elemento $a in A without {0}$ que no sea unidad se puede expresar como un producto finito de factores irreducibles de forma única salvo producto por unidades.
]

#proposition[
  Si $A$ es un DFU, $A[X]$ es un DFU.
]

#definition(title: "Dominio euclídeo")[
  Sea $A$ un dominio de integridad. 
  $A$ es un *dominio euclídeo* si existe una aplicación \
  $N: A without {0} -> NN$ tal que, dados $a, b in A, thick b != 0;$ existen $q, r in A$ tales que:

  - $a = b q + r$
  - $r = 0$ o $N(r) < N(b)$
]

#definition(title: "Dominio de ideales principales")[
  Un *dominio de ideales principales (DIP)* es un dominio de integridad cuyos ideales son todos principales.
]

#theorem[
  Todo dominio euclídeo es un DIP.
]

#theorem[
  Todo DIP es un DFU.
]

#important-box[
  $ "Dominio euclídeo" => "DIP" => "DFU" $
  Los recíprocos, en general, no son ciertos.
]

#proposition[
  Sea $A$ un DIP. Un ideal $I subset A$ es maximal si y solo si $I = angle.l p angle.r$ con p irreducible.
]

#theorem(title: "Teorema Fundamental del Álgebra")[
  Sea $P in CC[X]$ no constante. Entonces $P$ es irreducible en $CC[X]$ si y solo si $deg(P) = 1$.
]

#theorem[
  Si $P in RR[X]$ es irreducible en $RR[X]$ entonces $deg(P) <= 2$.
]

#lemma(title: "Lema de Gauss")[
  Un polinomio no constante $P = a_n x^n + ... + a_0 in ZZ[X]$ es irreducible en $ZZ[X]$ si y solo si $P$ es irreducible en $QQ[X]$ y $m c d (a_n, ..., a_0) = 1$.
]

#proposition(title: "Criterio de reducción módulo un primo")[
  Sea $Q(x) = a_n x^n + ... + a_0 in ZZ[X]$ y $p in ZZ$ primo.
  Sea $overline(Q(x)) = overline(a_n) x^n + ... + overline(a_0) in ZZ slash p ZZ [X]$.
  Supongamos que $deg(Q) = deg(overline(Q))$.
  Si $overline(Q(x))$ es irreducible en $ZZ slash p ZZ [X]$, entonces $Q(x)$ es irreducible en $QQ[X]$.
]

#pagebreak()

#proposition(title: "Criterio de Eisenstein")[
  Sea $Q(x) = a_n x^n + ... + a_1 x + a_0 in ZZ[X]$. Supongamos que existe $p in ZZ$ primo tal que:

  - $p divides a_i$ para $0 <= i < n$.
  - $p divides.not a_n$.
  - $p^2 divides.not a_0$.
  Entonces $Q(x)$ es irreducible en $QQ[X]$.
]

#tip-box(title: "Consejo: Hacer actuar automorfismo")[
  Sea $A$ un dominio de integridad. 
  Sea $phi.alt: A -> A$ un automorfismo de anillos.
  Un elemento $a in A$ es irreducible si y solo si $phi.alt(a)$ es irreducible.
]

#proposition(title: "Test de las raíces racionales")[
  Sea:
  $ P(x) = a_n x^n + ... + a_0 in ZZ[X], thick a_0, a_n != 0 $
  Si $r/s in QQ$ con $m c d (r, s) = 1$ es una raíz de $P(x)$ entonces $r divides a_0$ y $s divides a_n$ en $ZZ$.
]

= Extensiones de cuerpos

== Extensiones de cuerpos y característica

#definition(title: "Morfismo de cuerpos")[
  Sean $K, L$ dos cuerpos. Un *morfismo de cuerpos* $phi.alt: K -> L$ es un morfismo de anillos.
]

#lemma[
  Sea $K$ un cuerpo, $A$ un anillo (no nulo). Sea $phi.alt: K -> A$ un morfismo de anillos. Entonces $phi.alt$ es inyectivo. Es decir, todo morfismo de cuerpos es inyectivo.
]

#definition(title: "Extensión de cuerpos")[
  Sean $K, L$ cuerpos. Decimos que $L$ es una *extensión* de $K$ si existe un morfismo (inyectivo) de cuerpos $phi.alt: K -> L$. Denotamos la extensión mediante $L\/K$.

  En otras palabras, $L\/K$ es una extensión de cuerpos si $K$ es, salvo isomorfismo, un subcuerpo de $L$ ($K subset_! L$ y $+, dot$ coinciden en $K$ y $L$).
]

#definition(title: "Extensión simple")[
  Una extensión $L\/K$ es *simple* si existe $alpha in L$ tal que $L = K(alpha)$. Decimos que $alpha$ es un *elemento primitivo* de la extensión.
]

#theorem[
  Sean $K$ un cuerpo, $p(x) in K[X]$ un polinomio irreducible.
  El cuerpo $L := K[Y]/(angle.l p(y) angle.r)$ es una extensión de $K$ y el polinomio $p(x) in L[X]$ tiene la raíz $overline(y) in L$.
]

#pagebreak(weak: true)

#definition(title: "Característica de un cuerpo")[
  Un cuerpo $K$ (o anillo) tiene *característica* $n$, $"char"(K) = n$, si $n$ es el menor número natural tal que:
  $ underbrace(1_K + ... 1_K, n "veces") = 0 $

  Si esta suma fuera siempre distinta de $0$, decimos que $"char"(K) = 0$.
]

#lemma[
  Sea $K$ un cuerpo. Entonces $"char"(K) = 0$ o $"char"(K) = p$ un número primo.
]

#lemma[
  Si $phi.alt : K -> L$ es un morfismo de cuerpos, entonces $"char"(K) = "char"(L)$.
]

#corollary(numbering: none)[
  Si $L\/K$ es una extensión de cuerpos entonces $"char"(L) = "char"(K)$.
]

#proposition[
  Sea $K$ un cuerpo.

  - Si char$(K) = 0$, existe un único morfismo de cuerpos $ thick QQ -> K$.
  - Si char$(K) = p$, existe un único morfismo de cuerpos $ thick FF_p -> K$.
]<subcuerpo-primo>

#definition(title: "Cuerpo primo")[
  Un cuerpo es *primo* si no contiene subcuerpos propios. Dado un cuerpo $L$, su *subcuerpo primo* es el menor (para la inclusión) cuerpo $K subset L$.
]

#note-box[
  La @subcuerpo-primo implica que los únicos cuerpos primos son isomorfos a $QQ$ o $FF_p$, $ thick p$ primo.
  Además, Aut$(QQ) = {id}$ y Aut$(FF_p) = {id}$
]

#corollary[
  Sea $K$ un cuerpo.

  - Si char$(K) = 0$ entonces $K\/QQ$ es una extensión.
  - Si char$(K) = p$ entonces $K\/FF_p$ es una extensión.
]

== Grado de una extensión

#proposition[
  Sea $L\/K$ una extensión de cuerpos. Entonces $L$ es un espacio vectorial sobre $K$.
]

#definition[
  Sea $L\/K$ una extensión de cuerpos.

  - El *grado de la extensión*, $[L:K]$, es la dimensión de $L$ como $K$-espacio vectorial.
  - La extensión $L\/K$ es *finita* si $[L:K]$ es finito.
  - La extensión $L\/K$ es *infinita* si $[L:K]$ es infinito.
]

#theorem[
  Sean $K$ un cuerpo, $p(x) in K[X]$ un polinomio irreducible de grado $n$. Sea $L = K[X]/(angle.l p(x) angle.r)$.
  Entonces ${overline(1), overline(x), overline(x)^2, ..., overline(x)^(n-1)}$ es una base de $L$ como $K$-espacio vectorial, es decir,
  $ L = {a_0 + a_1 x + ... + a_(n-1) x^(n-1) | a_i in K} $

  En particular, $[L:K] = n$.
]

#corollary[
  Sea $K$ un cuerpo finito. Entonces $abs(K) = p^n$ para $p, n in NN, thick p$ primo.
]

#theorem(title: "Ley de la torre")[
  Sean $L\/K$ y $M\/L$ extensiones de cuerpos. Entonces:
  $ [M:K] = [M:L][L:K] $

  De hecho, si $L slash K$ y $M slash L$ son finitas y ${x_1, x_2, ..., x_r}$, ${y_1, y_2, ..., y_s}$ son sus bases, entonces ${x_i y_i | 1 <= i <= r, thick 1 <= j <= s}$ es una base de $M\/K$.
]

== Extensiones algebraicas


#definition[
  Sea $L\/K$ una extensión de cuerpos.

  - $alpha in L$ es *algebraico* sobre $K$ si existe un polinomio $p(x) in K[X]$ tal que $p(alpha) = 0$. 
  - $alpha in L$ es *trascendente* sobre $K$ si no es algebraico sobre $K$. 
]

#proposition[
  Sea $L\/K$ una extensión de cuerpos. Entonces son equivalentes:

  - $alpha in L$ es trascendente sobre $K$
  - $K[alpha] tilde.equiv K[X]$
  - $K(alpha) tilde.equiv K(x)$

  Como idea, si $alpha$ es trascendente, entonces se comporta como una indeterminada.
]

#pagebreak()

#definition[
  Se dice que una extensión $L\/K$ es:

  - *algebraica*, si todo $alpha in L$ es algebraico sobre $K$.
  - *trascendente*, si no es algebraica (existe $alpha in L$ trascendente sobre $K$)
]

#definition(title: "Polinomio mínimo")[
  Si $alpha$ es un elemento algebraico sobre un cuerpo $K$, se dice que $m_(alpha, K)(x) in K[X]$ es el *polinomio mínimo* de $alpha$ sobre $K$ si $m_(alpha, K)(x)$ es el polinomio mónico de menor grado en $K[X]$ tal que $m_(alpha, K)(alpha) = 0$.
]

#lemma[
  Sea $L\/K$ una extensión, $alpha in L$ algebraico sobre $K$. Se tiene que:

  - $m_(alpha, K)(x)$ es único
  - $m_(alpha, K)(x)$ es irreducible
  - Dado $p(x) in K[X]$, se tiene que $p(alpha) = 0 <=> m_(alpha, K)(x) divides p(x)$
  - Sea $K\/F$ una extensión, entonces $alpha$ es algebraico sobre $F$ y $m_(alpha, F)(x) divides m_(alpha, K)(x)$
  - Sea $p(x) in K[X]$ mónico con $p(alpha) = 0$. Entonces $p(x) = m_(alpha, K)(x) <=> p(x)$ es irreducible en $K[X]$.
]

#theorem[
  Sean $K$ un cuerpo, $p(x) in K[X]$ un polinomio irreducible. Sea $alpha$ una raíz de $p(x)$ en alguna extensión $L$ de $K$. Entonces tenemos un isomorfismo:

  $ K[Y]/(angle.l p(y) angle.r) -> K[alpha], thick "con" a in K -> a; thick overline(y) -> alpha $
]

#pagebreak()

#corollary[
  - Sean $K$ un cuerpo, $alpha$ un elemento algebraico sobre $K$. Entonces $K(alpha) = K[alpha]$.

  - Si $p(x) in K[X]$ es un polinomio irreducible sobre $K$ y $alpha, beta$ son dos raíces de $p(x)$, entonces:

  $ K(alpha) tilde.equiv K(beta) $
]

#corollary[
  Sean $K$ un cuerpo, $alpha$ un elemento algebraico sobre $K$. Entonces:

  - $[K(alpha):K] = deg(m_(alpha, K)(x))$

  - ${1, alpha, alpha^2, ... alpha^(deg(m_(alpha, K)(x)) - 1)}$ es una base de la extensión $K(alpha) \/ K$
]

#proposition[
  Toda extensión finita es algebraica.
]

#corollary[
  Sea $L\/K$ una extensión de cuerpos. Si $alpha in L$ es algebraico sobre $K$ entonces $K(alpha) \/ K$ es algebraica.
]

#proposition[
  Una extensión $L\/K$ es finita si y solo si $L$ está generado por un número finito de elementos algebraicos sobre $K$.
]

#theorem[
  Si las extensiones $F\/K$ y $L\/F$ son algebraicas, entonces $L\/K$ es algebraica.
]

#corollary[
  Sea $L\/K$ una extensión de cuerpos. Sea $F = {alpha in L | alpha "es algebraico sobre" K}$.
  Entonces $F$ es un cuerpo y $F\/K$ es una extensión algebraica.
]

#proposition[
  Una extensión de cuerpos $L\/K$ es de grado infinito si y solo si se da una de las situaciones siguientes:

  - $L\/K$ es una extensión trascendente.
  - $L\/K$ es una extensión algebraica que no está finitamente generada.
]


== Tres problemas clásicos

#emph-box[
  I) _Duplicación del cubo_ $arrow$ Dado un cubo, construir otro de volumen doble.

  II) _Trisección de un ángulo_ $arrow$ Dado un ángulo $theta$, construir $theta/3$.

  III) _Cuadratura del círculo_ $arrow$ Dado un círculo, construir un cuadrado de la misma área.
]

#definition(title: "Números constructibles")[
  Un *número constructible* es una longitud que puede ser construida con regla y compás (a partir de la longitud 1).
]

#lemma[
  Sea $K$ el conjunto de los números constructibles. Si $a, b$ son constructibles $(a, b in K)$, podemos contruir: $a + b$, $a - b, thick a b, thick a\/b, thick sqrt(a)$. Luego $K$ es un cuerpo.
]

#theorem[
  Un número real $x$ es constructible si y solo si pertenece a un cuerpo $L subset RR$ tal que existe una cadena de subcuerpos $thick QQ = L_0 subset L_1 subset L_2 subset ... subset L_n = L$ donde todas las extensiones $L_(i+1) \/ L_i$ son de grado $2$.
]

#corollary[
  Si $x in RR$ es constructible, entonces $[QQ(x):QQ] = 2^n$ para algún $n in NN$.
]

#theorem[
  Ninguna de las construcciones (I), (II), (III) es posible.
]

= Extensiones de Galois

== Cuerpo de descomposición y clausura algebraica

#definition(title: "Cuerpo de descomposición")[
  Sean $K$ un cuerpo, $p(x) in K[X]$ con $deg(p(x)) = n >= 1$.
  Una extensión $L\/K$ es un *cuerpo de descomposición* de $p(x)$ (sobre $K$) si:

  - $p(x)$ se descompone en factores lineales en $L[X]$ (decimos que $p(x)$ se descompone completamente en $L[X]$), es decir, se tiene que:

  $ p(x) = u (x-alpha_1)(x-alpha_2)...(x-alpha_n) $

  - $p(x)$ no se descompone completamente en ningún subcuerpo propio de $L$ que contenga a (la imagen de) $K$.
]

#definition(title: "K-isomorfismo")[
  Sean $K, A, B$ cuerpos con $K subset A$ y $phi.alt: A -> B$ un isomorfismo.
  Decimos que $phi.alt$ es un \ *$K$-isomorfismo* si deja fijo a $K$.
]

#proposition[
  Sean $K$ un cuerpo, $p(x) in K[X]$ un polinomio.
  Existe un cuerpo de descomposición $L$ de $p(x)$ sobre $K$ que es único salvo $K$-isomorfismos (la imagen de $K$ en $L$ vía el morfismo de la extensión).
]

#corollary[
  Sean $K$ un cuerpo, $p(x) in K[X]$ y $L$ el cuerpo de descomposición de $p(x)$.
  Entonces: $ [L:K] <= n!, quad n = deg(p(x)) $
]

#note-box[
  Dado un cuerpo $K$, el cuerpo de descomposición es una extensión de $K$ que contiene todas las raíces de *un* polinomio sobre $K$.
  Ahora queremos una extensión que contenga *todas* las raíces de *todos* los polinomios sobre $K$.
]

#definition(title: "Clausura algebraica")[
  Sea $K$ un cuerpo.
  Una extensión algebraica $overline(K) slash K$ es una *clausura algebraica* de $K$ si todo polinomio $p(x) in K[X]$ se descompone completamente sobre $overline(K)$.

  Podemos decir que $overline(K)$ contiene todos los elementos algebraicos sobre $K$.
]

#proposition[
  Sea $K$ un cuerpo.
  Existe una clausura algebraica de $K$ que es única salvo $K$-isomorfismo.
]

#important-box[
  Todos los "cálculos" que involucren elementos algebraicos sobre un cuerpo $K$ pueden verse como cálculos en un cuerpo "grande", $overline(K)$.
]

#definition(title: "Cuerpo algebraicamente cerrado")[
  Un cuerpo $K$ es *algebraicamente cerrado* si todo polinomio con coeficientes en $K$ tiene una raíz en $K$.
  Esto implica que todas sus raíces están en $K$, pues descompone completamente:

  $ p(x) = (x-alpha_1)p_1(x) = (x-alpha_1)(x-alpha_2)p_2(x) = ... = (x-alpha_1) ... (x-alpha_n) $

  Equivalentemente, $K$ es *algebraicamente cerrado* si $K = overline(K)$.
]

#proposition[
  Sean $K$ un cuerpo, $overline(K)$ su clausura algebraica.
  Entonces $overline(K)$ es algebraicamente cerrado.
]

#theorem(title: "Teorema Fundamental del Álgebra")[
  El cuerpo $CC$ es algebraicamente cerrado. En particular, $CC = overline(RR)$
]

#let a = [Clausura algebraica de $QQ$]

#definition(title: a)[
  La clausura de $QQ$ se define como:
  $ {a in CC : a "es algebraico sobre" QQ} $

  A este cuerpo también se le llama *cuerpo de números algebraicos* de $QQ$, y es una extensión algebraica infinita de $QQ$.
]

== Extensiones normales

#definition(title: "Extensión normal")[
  Una extensión algebraica es *normal* si todo polinomio irreducible $p(x) in K[X]$ que tiene una raíz en $L$ se descompone completamente en $L[X]$.
]

#proposition[
  Una extensión $L slash K$ es normal y finita si y solo si $L$ es un cuerpo de descomposición de un polinomio de $K[X]$.
]

== Extensiones separables

#definition(title: "Raíces simples y múltiples")[
  Sean $K$ un cuerpo, $p(x) in K[X]$ un polinomio.
  Sobre un cuerpo de descomposición $L$ de $p(x)$ tenemos:

  $ p(x) = (x - alpha_1)^(m_1) (x - alpha_2)^(m_2) ... (x - alpha_r)^(m_r); thick thick thick alpha_i in L, thick alpha_i != alpha_j, thick m_i >= 1 $

  Entonces $alpha_i$ es una *raíz simple* si $m_i = 1$ y es *múltiple* si $m_i > 1$ (con multiplicidad $m_i$).
]

#definition(title: "Cosas separables")[
  Sea $L slash K$ una extensión algebraica.

  - Un polinomio $p(x) in K[X]$ es *separable* si no tiene raíces múltiples (en cualquier cuerpo de descomposición).

  - Un elemento $alpha in L$ es *separable* sobre $K$ si $m_(alpha, K) (x)$ es separable.

  - La extensión $L slash K$ es *separable* si todo $alpha in L$ es separable sobre $K$.

  - Un polinomio, elemento o extensión que no es separable se dice que es *inseparable*.
]

#definition(title: "Derivada formal")[
  Dado un polinomio $p(x) = a_n x^n + a_(n-1) x^(n-1) + ... + a_1 x + a_0$ en $K[X]$, su *derivada formal* es:

  $ p'(x) = n a_n x^(n-1) + (n-1) a_(n-1) x^(n-2) + ... + 2 a_2 x + a_1 in K[X] $
]

#proposition[
  Sean $K$ un cuerpo, $p(x) in K[X]$, $L$ un cuerpo de descomposición de $p(x)$.
  Entonces:

  - $p(x)$ tiene una raíz múltiple $alpha in L$ si y solo si $alpha$ también es una raíz de $p'(x)$.
  - $p(x)$ es separable si y solo si $"mcd"(p(x), p'(x)) = 1$ en $K[X]$.
]

#corollary[
  Un polinomio irreducible $p(x) in K[X]$ es inseparable si y solo si $p'(x) equiv 0$.
]

#corollary[
  Sea $K$ un cuerpo de característica $0$. Entonces:

  - Todo polinomio irreducible en $K[X]$ es separable.
  - Un polinomio en $K[X]$ es separable si y solo si es el producto de polinomios irreducibles distintos.
]

#note-box[
  En característica $p>0$, sí hay anulaciones al derivar:

  $ (x^(p m))' = p m x^(p m - 1) = 0 $

  Y esto puede ocurrir también para polinomios irreducibles.
]

#proposition(title: "Endomorfismo de Frobenius")[
  Sea $K$ un cuerpo con $"char"(K) = p > 0$.
  La aplicación $phi: K -> K$ con $a -> a^p$ es un morfismo de cuerpos, llamado el *endomorfismo de Frobenius*.

  El endomorfismo de Frobenius es inyectivo (es un morfismo de cuerpos).
  Es interesante la situación en la que también es sobreyectivo (luego automorfismo).
]

#definition(title: "Cuerpo perfecto")[
  Un cuerpo $K$ es *perfecto* si $"char"(K) = 0$ o bien $"char"(K) = p$ y $K=K^p$, es decir, que todo elemento de $K$ es una potencia $p$-ésima (o admite una raíz $p$-ésima).
]

#lemma[
  Todo cuerpo finito es perfecto.
]

#theorem[
  Sea $K$ un cuerpo perfecto.

  - Todo polinomio irreducible en $K[X]$ es separable.

  - Un polinomio en $K[X]$ es separable si y solo si es el producto de polinomios irreducibles distintos.
]

#theorem(title: "Existencia y unicidad de cuerpos finitos")[
  Para $n in NN, thick n>=1$ y $p$ primo, existe un cuerpo con $p^n$ elementos que es único salvo #linebreak(justify: true) $FF_p$-isomorfismo.
]

#theorem(title: "Teorema del elemento primitivo")[
  Si $L slash K$ es una extensión separable finita, entonces es simple (es decir, $exists alpha in L : L = K(alpha)$).
]

= El Teorema Fundamental de la Teoría de Galois

== Automorfismos de cuerpos

#definition(title: "Morfismo de cuerpos")[
  Sean $K$ un cuerpo, $F slash K$ y $L slash K$ dos extensiones.
  Un *morfismo de cuerpos* $phi: F -> L$ es un $K$-morfismo (o morfismo de extensiones) si $phi|_K = id_K$ ($phi(a) = a "para" a in K$).

  #align(center,
    diagram(cell-size: 15mm, $
	  F edge(phi, ->) edge("d", <-) & L \
	  K edge("r", phi|_K = id_K,->) & K edge("u", ->)
  $)
  )
]

#proposition[
  Sean $F, L$ cuerpos, $phi: F -> L$ un morfismo de cuerpos, $K subset F$ el subcuerpo primo de $F$. Entonces:

  - $K$ es también el subcuerpo primo de $L$ (salvo isomorfismo).
  - $phi$ es un $K$-morfismo.
]

#lemma[
  Sean $K$ un cuerpo, $F slash K$ y $L slash K$ extensiones, $sigma : F -> L$ un $K$-morfismo.
  Sea $alpha in F$ algebraico sobre $K$ y $p(x) in K[X]$ un polinomio del que $alpha$ es raíz.
  Entonces $sigma(alpha) in L$ es raíz de $p(x)$.

  $
  p(x) in K[X] arrow cases(p(x) in F[X] &arrow p(alpha) &= 0 &"en" F, p(x) in L[X] &arrow p(sigma(alpha)) &= 0 &"en" L)
  $
]

#lemma[
  Sean $K$ un cuerpo, $F slash K$ y $L slash K$ extensiones, $cal(B)$ una base de $F$ como $K$-espacio vectorial.
  Sea $sigma: F -> K$ un morfismo de $K$-esepacios vectoriales.
  Entonces $sigma$ es un $K$-morfismo de cuerpos si y solo si $sigma(alpha alpha') = sigma(alpha) sigma(alpha')$ para todos $alpha, alpha' in cal(B)$.
]

#important-box[
  Los $K$-morfismos de cuerpos están determinados por las imágenes de los elementos de una base si estas son compatibles con el producto.
]

#proposition[
  - Si $[K(alpha): K] = n$, $L$ contiene a un cuerpo de descomposición de $m_(alpha, K) (x)$ sobre $K$ y $m_(alpha, K) (x)$ es separable, entonces hay $n = "deg"(m_(alpha, K) (x))$ $K$-morfismos $K(alpha) -> L$ distintos.
  - Buscando morfismos de la forma $K(alpha_1, alpha_2, ..., alpha_r) -> L$. Si $m_(alpha_i, K(alpha_1, alpha_2, ..., alpha_(i-1))) (x)$ tiene la misma expresión que $m_(alpha_i, K) (x)$ para $2 <= i <= r$, entonces todas las combinaciones de raíces de $m_(alpha_j, K) (x)$ son imágenes válidas de $alpha_j$ en un $K$-morfismo de cuerpos.
    Es decir, hemos encontrado una *condición suficiente*.
]

#definition(title: "Grupo de automorfismos")[
  Sea $K$ un cuerpo. Entonces:

  - Un isomorfismo $sigma: K -> K$ se llama un *automorfismo* de $K$.

  - El conjunto de automorfismos de $K$ se denota *$"Aut"(K)$*.
  
  - Si $L slash K$ es una extensión, el conjunto de $K$-automorfismos de $L$ se denota *$"Aut"(L slash K)$*.
]

#lemma[
  Sea $L slash K$ una extensión algebraica.
  Entonces todo $K$-endomorfismo de $L$ es un $K$-automorfismo.
]

#lemma[
  Sean $K$ un cuerpo, $L slash K$ una extensión.
  Entonces $("Aut"(L), compose, id_L)$ es un grupo y $("Aut"(L slash K), compose, id_L)$ es un subgrupo.
]

#definition(title: "Cuerpo fijo")[
  Sean $K$, $L slash K$ una extensión, $H$ un subgrupo de $"Aut"(L slash K)$.
  El conjunto
  $ L^H = {a in L : forall h in H thick thick h(a) = a} $

  es un subcuerpo de $L$, llamado el *cuerpo fijo* de $H$.
]

#important-box[
  Tenemos dos correspondencias:

  - Subcuerpos de $L arrow$ Subgrupos de $"Aut"(L) wide arrow wide K -> "Aut"(L slash K)$.

  - Subgrupos de $"Aut"(L) arrow$ Subcuerpos de $L wide arrow wide H arrow L^H$.

  La siguiente proposición nos dice que revierten las inclusiones.
]

#proposition[
  Sean $K$ un cuerpo, $L slash K$ una extensión.

  - Si $K_1 subset.eq K_2 subset.eq L$ son dos subcuerpos de $L$, entonces $"Aut"(L slash K_2) <= "Aut"(L slash K_1)$.

  - Si $H_1 <= H_2 <= "Aut"(L slash K)$ son dos subgrupos de $"Aut"(L slash K)$, entonces $K subset.eq L^(H_2) subset.eq L^(H_1)$.
]

#note-box[
  Nos gustaría que la correspondencia entre subgrupos de $"Aut"(L slash K)$ y subcuerpos de $L$ que contienen a $K$ fuese perfecta.
  Necesitamos $"Aut"(L slash K)$ sea lo más grande posible. Para ello buscamos que $L slash K$ sea *normal* y *separable*.
]

#lemma[
  Sea $L slash K$ una extensión. Sean $sigma_1, sigma_2, sigma_r in "Aut"(L slash K)$ automorfismos distintos.
  Entonces son linealmente independientes sobre $L$.
  Es decir, si $lambda_1, ..., lambda_r in L$ no son todos nulos, entonces:

  $
  lambda_1 sigma_1 + lambda_2 sigma_2 + ... + lambda_r sigma_r: L &-> L \
  a &-> lambda_1 sigma_1(a) + lambda_r sigma_r (a)
  $

  no es el morfismo de grupos nulo $L -> L; thick a -> 0$.
]

#proposition[
  Sean $L slash K$ una extensión y $H$ un subgrupo finito de $"Aut"(L slash K)$.
  Entonces:

  $ [L : L^H] = |H| wide "y" wide [L^H : K] = ([L:K])/(|H|) $
]

#corollary[
  Sea $L slash K$ una extensión finita.
  Entonces 
  $ |"Aut"(L slash K)| <= [L : K] $

  y $|"Aut"(L slash K)| = [L : K]$ si y solo si $K = L^("Aut"(L slash K))$.
]

#important-box[
  - Ya hemos visto que, si $L slash K$ es una extensión y $p(x) in K[X]$ es irreducible, todo $K$-automorfismo de $L$ debe permutar las raíces de $p(x)$ en $L$.

  - No es cierto que para toda permutación haya un $K$-automorfismo que la efectúe, pero sí que, fijadas dos raíces de $p(x)$ en $L$, hay un $K$-automorfismo que lleva una en la otra.
]

#proposition[
  Sean $L slash K$ una extensión normal y finita, $M_1 slash K$ y $M_2 slash K$ dos subextensiones.
  Si $psi: M_1 -> M_2$ es un $K$-isomorfismo, entonces existe $sigma in "Aut"(L slash K)$ tal que $sigma|_(M_1) = psi$.
]
