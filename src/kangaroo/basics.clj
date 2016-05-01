(ns kangaroo.basics
  (:require [kangaroo.core :as seql]))

; a single 'expresion' is for example 'a, or '() but 'a 'b is not because they
; are two elements. Nevertheless '[a b] is a form because it is a single vector
; which contains two values. Other fundamental types work the same
(defn expression [input] (or (sequential? input) (string? input)
                             (symbol? input) (number? input)
                             (map? input) (set? input) (keyword? input)))

(defn vec-form [sub-form] (seql/and vector? (seql/subex sub-form)))
(defn list-form [sub-form] (seql/and list? (seql/subex sub-form)))
(defn map-form [sub-form] (seql/and map? (seql/subex sub-form)))

(defn map-pair [k-form v-form] (seql/subex (seql/cat k-form v-form)))

(declare binding-form)

(def binding-vec "a binding vector a.k.a vector destructuring.
  Used inside fn args, let expressions and similars"
  (vec-form (seql/cat (seql/rep* (delay binding-form))
                      (seql/opt (seql/cat '& symbol?))
                      (seql/opt (seql/cat :as symbol?)))))

(def binding-map "a binding map a.k.a map destructuring.
  Used inside fn args, let expressions and similars"
  (map-form (seql/cat (seql/rep* (map-pair (delay binding-form) expression))
                      (seql/opt  (map-pair :as symbol?))
                      (seql/opt  (map-pair (seql/alt :keys :strs :syms)
                                           (vec-form (seql/rep* symbol?))))
                      (seql/opt  (map-pair :or (map-form (seql/rep* (map-pair symbol? expression))))))))

(def binding-form "a binding form, such as a symbol or a vector or map
  destructuring. The first element of the couple that are used in let expressions"
  (seql/alt symbol? binding-vec binding-map))

(def binding-pair "a binding pair, only useful in let expressions (a.f.a.i.k)"
  (seql/cat binding-form expression))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(seql/exec binding-map
           '({[a b] :a d :d}))

(seql/exec (map-pair (delay binding-form) expression)
           '([a :b]))

