(ns kangaroo.syntaxes
  (:require [kangaroo.core  :as seql]
            [kangaroo.reporter :as report]
            [kangaroo.rules :as rule]))

(defn docstring [o] (string? o))
(defn meta-map [o] (map? o))
(defn prepost [o] (map? o))

(def args rule/binding-vec)
(def body (seql/cat args (seql/opt prepost) (seql/rep* rule/expression)))
(def bodies (seql/rep+ (rule/list-form body)))

(def fn-syntax (seql/cat 'fn (seql/opt symbol?)
                         (seql/alt body bodies)))

(def defn-syntax
  (seql/cat 'defn symbol?
            (seql/opt docstring)
            (seql/opt meta-map)
            (seql/alt body bodies)))

(def if-syntax
  (seql/cat 'if rule/expression rule/expression (seql/opt rule/expression)))

(def let-syntax
  (seql/cat 'let (rule/vec-form (seql/rep* rule/binding-pair))
             (seql/rep* rule/expression)))

(def do-syntax
  (seql/cat 'do (seql/rep* rule/expression)))

(def loop-syntax
  (seql/cat 'loop rule/binding-vec rule/expression))


; ------------ EXAMPLE ------------;

; introduce a grammar error and watch the output error
;PS: it works best printing on the console

(def bar '(defn bar2 "docstring"
            {data1 "value1" data2 "value2"}
            [arg1 arg2] ;comment
            (let [{:keys (a c) :or {a 3 c 4}} arg1
                  :b [1 2]
                  lulu (fn [r t] [r t])]
              (if (= a b)
                (+ a b)
                (a (dec b))))))

(def foo '(let [{:keys [a c] :or {a 3 c 4}} arg1
                  b [1 2]
                  lulu (fn [r t] [r t])]
              (if (= a b)
                (+ a b)
                (a (dec b)))))

(println (report/report (seql/exec let-syntax foo)))
