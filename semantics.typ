//#import "@preview/ilm:1.4.1": *
// #import cosmos.rainbow: *
// #import cosmos.clouds: *
// seems more performant than doing queries for each of these

#let math_names = state("math_names", (:))
#let names(label, ..words, plural: false) = {
  math_names.update(x => {
    for word in words.pos() {
      x.insert(lower(word), label)
      if plural {
        x.insert(lower(word) + "s", label)
      }
    }
    x
  })
}
#let strify(content) = if type(content) == str {
  content
} else if content.has("text") {
  content.text
} else if content.has("body") {
  strify(content.body)
} else if content.has("child") {
  strify(content.child)
}
#let name(label, word, plural: false) = names(label, (word), plural)
#let refname(word, instead) = context link(math_names.get().at(lower(strify(word))), text(rgb(60,0,60),(if instead != none {
  instead
} else {
  word
})))
#let n(w) = refname(w, none)
#let nn(w, ctx) = refname(strify(ctx)+"."+strify(w),w)
#let def(label, definiens, verbatim: false) = {
  if verbatim {
    [#definiens#label]
  } else {
    [#emph[#definiens]#label]
  }}

#let justify(label, symbol, comment: none) = {
  $#symbol^#(link(label, sym.quest) + if comment != none {
    footnote(comment)})$}

#let justifyt(label, comment: none) = {
  (link(label, super(sym.quest)) + if comment != none {
    footnote(comment)})}


#let refvar(var, varrender, location) = context {  
  let loc = if location == none {
    here() 
  } else {
    location
  }
  let figure = if location == none { query(selector(<theorion-frame-metadata>).before(loc)).last() }else {query(selector(<theorion-frame-metadata>).after(loc)).first()}
  //repr(figure)
  let figure-loc = figure.location()
  let metadata-loc = query(metadata.where(value: (var: var)).after(figure-loc).before(here()))
  if metadata-loc == () {
    panic(repr(figure-loc.position()) + var + " has not been declared")
  }
  if location == none {
    
    link(metadata-loc.last().location(), varrender)
  } else {
    link(metadata-loc.first().location(), varrender)
  }
}

/// declare var
#let dv(var) = [#metadata((var: repr(var))) #text(rgb(90,10,10),var)]
/// reference var
#let rv(var) = context refvar(repr(var),var, none)

//#show math.text: it2 => if it2 == [S] {[T]} else {it2}
/// keep referencing var in equation, only works for single letter stuff due to typst not having any actually decent query features
#let kv(..vars) = if vars.pos().all(x => x.text.len() == 1) { [#metadata((keepvar: vars.pos()))]} else {panic("only single character vars work for kv at the moment")}
/*
#show math.equation: it => if it.has("body") and it.body.has("children") and it.body.children.find(x => x.has("value") and x.value.at("keepvar", default: none) != none) != none {
  
  let vars = it.body.children.find(x => x.has("value") and x.value.at("keepvar", default: none) != none).value.at("keepvar").map(x => x.text)
  [#show regex(vars.join("|")): it => rv(it)
   #it]
} else {
  it
}
*/
/*
#show figure: it => if it.has("body") and it.body.has("children") and it.body.children.at(0).value.body.children.find(x => x.has("value") and x.value.at("keepvar", default: none) != none) != none {
  
  let vars = it.body.children.at(0).value.body.children.find(x => x.has("value") and x.value.at("keepvar", default: none) != none).value.at("keepvar").map(x => x.text)
  [#show math.equation: it2 =>[
    #show regex(vars.join("|")): it3 => rv(it3)
    #it2]
   #it]
} else {
  it
}
*/
#let lk(..args) = text(rgb(60,0,60), link(..args))

// no v!

#let ra = $rv(a)$
#let rb = $rv(b)$
#let rc = $rv(c)$
#let rd = $rv(d)$
#let re = $rv(e)$
#let rf = $rv(f)$
#let rg = $rv(g)$
#let rh = $rv(h)$
#let ri = $rv(i)$
#let rj = $rv(j)$
#let rk = $rv(k)$
#let rl = $rv(l)$
#let rm = $rv(m)$
#let rn = $rv(n)$
#let ro = $rv(o)$
#let rp = $rv(p)$
#let rq = $rv(q)$
#let rr = $rv(r)$
#let rs = $rv(s)$
#let rt = $rv(t)$
#let ru = $rv(u)$
#let rw = $rv(w)$
#let rx = $rv(x)$
#let ry = $rv(y)$
#let rz = $rv(z)$
#let rA = $rv(A)$
#let rB = $rv(B)$
#let rC = $rv(C)$
#let rD = $rv(D)$
#let rE = $rv(E)$
#let rF = $rv(F)$
#let rG = $rv(G)$
#let rH = $rv(H)$
#let rI = $rv(I)$
#let rJ = $rv(J)$
#let rK = $rv(K)$
#let rL = $rv(L)$
#let rM = $rv(M)$
#let rN = $rv(N)$
#let rO = $rv(O)$
#let rP = $rv(P)$
#let rQ = $rv(Q)$
#let rR = $rv(R)$
#let rS = $rv(S)$
#let rT = $rv(T)$
#let rU = $rv(U)$
#let rV = $rv(V)$
#let rW = $rv(W)$
#let rX = $rv(X)$
#let rY = $rv(Y)$
#let rZ = $rv(Z)$