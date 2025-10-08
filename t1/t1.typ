#import "@preview/theorion:0.4.0": *
#import cosmos.rainbow: *
#show: show-theorion

#set heading(numbering: "1.")
#set text(lang: "es")

// 1. Change the counters and numbering:
#set-inherited-levels(1)
#set-zero-fill(true)
#set-leading-zero(true)
#set-theorion-numbering("1.")

// 2. Other options:
// #set-result("noanswer") // Elimina las demostraciones
#set-qed-symbol[#math.qed]

#set page(
    paper: "a4",
    margin: (x: 2.5cm, y: 3cm),
)

#set text(12pt)

#align(center)[
  #text(size:20pt)[
    *CHULETARIO ÁLGEBRA II*
  ]

  #text(size:12pt)[
    *2025 \~ 2026*
  ]
]

#outline()


#counter(page).update(1)

#set page(
  margin: (x: 2.5cm, y: 2.5cm),
  header: [
    a
    #h(1fr) 
    a \
    #line(length: 100%)],
    numbering: "1"
  )

= Repaso de teoría de cuerpos
== Anillos y cuerpos
== Ideales y cocientes
== Factorización en anillos de polinomios

= Extensiones de cuerpos
== Extensiones algebraicas
== Cuerpos finitos
== Grado de una extensión de cuerpos
== Polinomio mínimo
== Aplicación a las construcciones con regla y compás

= Extensiones de Galois
== El cuerpo de descomposición de un polinomio
== Clausura algebraica

#theorem(title: "aaaa")[
  afdjsakfjskl.
]

#proof()[
  Este es el cuerpo de la demostración.
]
