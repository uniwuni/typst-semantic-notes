#import "semantics.typ": *
#import "@preview/theorion:0.3.3": *
#import cosmos.fancy: *
#import "@preview/quick-maths:0.2.1": shorthands
#set text(lang: "en")
#show: show-theorion
#import "@preview/ilm:1.4.1": *

#set text(lang: "en")

#show: ilm.with(
  title: [Mathematics],
  author: "Uni",
  external-link-circle: false,
  bibliography: bibliography("notes/bib.yml"),
  figure-index: (enabled: true),
  table-index: (enabled: true),
  listing-index: (enabled: true)
)

/*
#definition(title: "Injectivity")[
  A function $dv(f) : dv(A) -> dv(B)$ is called #def(<inj>)[injective], if, for all $dv(a), dv(a') in rv(A)$, 
  #kv([f]) $f(rv(a)) = f(rv(a'))$ implies $rv(a) = rv(a')$.
]
#names(<inj>, "injective", "injection", "injections", "injectivity", "one-to-one")

#definition(title: "System of Natural numbers")[
  #def(<nat-num-sys>)[A system of natural numbers] is a tuple $(dv(NN), dv(0), dv(S))$ #kv([0], [S]) such that 
   + $0 in rv(NN)$,
   + $S : rv(NN) -> rv(NN)$,
   + for all $dv(n) in rv(NN)$, $0 eq.not S(rv(n))$,
   + $S$ is #n[injective].
   + for all sets $dv(A) subset.eq rv(NN)$ with $rv(0) in rv(A)$ and $rv(A)$ closed under $rv(S)$, we have $rv(A) = rv(S)$.
]

#names(<nat-num>, plural: true, "natural number", "nonnegative integer")
*/
= Foundations
#include "notes/001logic.typ"
#include "notes/002sets.typ"
