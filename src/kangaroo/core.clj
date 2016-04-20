(ns kangaroo.core
  (:refer-clojure :rename {cat clj-cat, and clj-and})
  (:require [clojure.string :as string]
            [clojure.data.int-map :refer [int-map]]
            [clojure.main :refer [demunge]]))

;TODO change name to barbara !!

(defonce ^:private id-counter (atom 0))
(defn- mk-id [] (swap! id-counter inc))

(comment the drill goes like this\:
  we convert everything to an NFA\; those are composed of nodes, each one with
  predicate to check an input against. we then connect those NFAs such that
  they form a single one. Nested NFAs are possible, thus checking if they match
  an input is conditional with the kind of object that we are checking against.
  Nested NFAs return a verdict object to avoid rechecking the input to build up
  an error message.
  Peace !)

(defprotocol NfaPlugable "protocol definition required to convert a certain
  type into an NFA"
  (->automat [object] "takes an object and wraps it in an NFA"))

(defprotocol Judment "protocol to compare an input against an object rules"
  (judge [object input] "judge is input fulfills object's rules. returns true or false"))

(defprotocol Statement
  (holds? [object] "check the result of a judgment"))

(defprotocol Bypasser "protocol to get the output of (split-)node"
  (peep [anode nodes] "return a hash-map of {id node} nodes that anode leads to"))

(defprotocol Mechanic "protocol for patching up nodes with dangling out*"
  (connect [node id] "set a dangling out* in node to id"))

;; FIXME I don't do a lot yet
;; a verdict of comparing an input against an object rule(s)
(defrecord verdict  [ok? msg])

(extend-protocol Statement
  java.lang.Boolean
  (holds? [object] object)
  verdict
  (holds? [object] (:ok? object)))

(declare exec)
;; a NonDeterministic Finite Automat with first node id fid and an integer
;; hash-map of nodes
(defrecord nfa [fid nodes]
  NfaPlugable
  (->automat [object] object)
  Judment ;FIXME implement the whole NFA checking process here
  (judge [object input] (exec object input)))

;; an NFA state with (possible) eps transitions, a predicate to compare input against,
;; and two possible output states
(defrecord node [id name pred out] ; one arrow out
  NfaPlugable
  (->automat [object] (map->nfa {:fid (:id object) :nodes (int-map (:id object) object)}))
  Statement
  (holds? [object] object); no-op, return it as it is
  Bypasser ;; everything you want is here; no need to look for more ;)
  (peep [anode nodes] (apply int-map (find nodes (:id anode))))
  Mechanic
  (connect [object id] (if (nil? (:out object))
                         (int-map (:id object) (assoc object :out id))
                         (int-map (:id object) object))))

;; an NFA state with *only* eps transitions and two possible output states
;; unlabeled arrows in out and out1 (if-not (nil? out*))
(defrecord split-node [id out out1]
  Mechanic
  (connect [object id] (if (nil? (:out1 object))
                         (int-map (:id object) (assoc object :out1 id))
                         (int-map (:id object) object)))
  Bypasser
  (peep [anode nodes] (merge (peep (get nodes (:out  anode)) nodes)
                             (when-let [arrow (:out1 anode)]
                               (peep (get nodes arrow) nodes)))))

(extend-type java.lang.Object
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred #(= % object) :name (str object)}))))

(extend-type clojure.lang.IFn
  Judment
  (judge [object input] (object input))
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred object :name (demunge (str object))}))))

;;  SINGLETON object
(defonce ^:const ^:private END (map->node {:id 0 :name "END" :pred (fn [input] false)}))

;; (defn- name-it
;;   "given a checker function and a state type return the unmangled function name"
;;   [checker stype]
;;   (cond (= stype END) "END"
;;         (nil? checker) nil
;;         :else (string/replace (second (re-find #"^.+\$(.+)\@.+$" (str checker)))
;;                               #"\_QMARK\_" "?")))

(defn cat
  "concatenate two or more objects"
  ([object] (->automat object))
  ([object object2]
   (let [auto1 (->automat object)
         auto2 (->automat object2)
         new-states (apply merge (map connect (vals (:nodes auto1))
                                        (repeat (:fid auto2))))]
                (assoc auto1 :nodes (merge new-states (:nodes auto2)))))
  ([object object2 & more-objects]
   (reduce cat (cat object object2) more-objects)))

(defn alt
  "alternate between two or more objects"
  ([object object2]
   (let [auto1 (->automat object)
         auto2 (->automat object2)
         split (map->split-node {:id (mk-id) :out (:fid auto1) :out1 (:fid auto2)})]
     (map->nfa {:fid (:id split) :nodes (merge (:nodes auto1)
                                               (int-map (:id split) split)
                                               (:nodes auto2))})))
  ([object object2 & more-objects]
   (reduce alt (alt object object2) more-objects)))

(defn opt
  "optional object"
  [object]
    (let [auto  (->automat object)
          split (map->split-node {:id (mk-id) :out (:fid auto)})]
      (map->nfa {:fid (:id split) :nodes (merge (:nodes auto) (int-map (:id split) split))})))

(defn rep*
  "zero or more repetitions of the object"
  [object]
    (let [auto  (->automat object)
          split (map->split-node {:id (mk-id) :out (:fid auto)})]
      (map->nfa {:fid (:id split) :nodes (into (int-map (:id split) split)
                                               (map connect (vals (:nodes auto))
                                                            (repeat (:id split))))})))

(defn rep+
  "one or more repetitions of the object"
  [object]
  (let [auto  (->automat object)
        split (map->split-node {:id (mk-id) :out (:fid auto)})]
    (map->nfa {:fid (:fid auto) :nodes (into (int-map (:id split) split)
                                             (map connect (vals (:nodes auto))
                                                          (repeat (:id split))))})))

(defn and ;; implemented as an NFA inside the NFA under construction
  [object object2 & more]
  (let [machine (reduce cat (cat object object2) more)
        nest    (->node (mk-id) "FIXME" machine nil)]
    (map->nfa {:fid (:id nest) :nodes (int-map (:id nest) nest)})))

(defn- next-states
  "given a sequence of nodes (not split nodes) and a hash-map with all possible
  nodes, return the sequence of all states that 'states' lead to"
  [states nodes]
  (let [all-out  (map #(get nodes (:out %)) states)
        literals (filter :pred all-out)
        splits   (remove :pred all-out)]
    (distinct (concat literals
                      (sequence (comp (map peep) (mapcat vals))
                                splits (repeat nodes))))))

(defn- error
  "returns a string with the error message of an unsucessfull match"
  [error-type input states]
  (condp = error-type
    :extra (str "too many elements: " (str input))
    :missing (str "missing elements: \n Expected any of "
                  (string/join ", " (map :name states)))
    :mismatch (str "Expected any of: " (string/join ", " (map :name states))
                   "; instead got: " (str input))))

(defn- end? [state] (= END state))

(defn- stop?
  [states input]
  (let [end-found   (some end? states)
        empty-input (empty? input)]
    (cond
      ;; too much input, not enough states
      (clj-and end-found (not empty-input)) (->verdict false (error :extra input states))
      ;; success !
      (clj-and end-found empty-input) (->verdict true :msg nil)
      ;; missing input
      (clj-and empty-input (not-empty states)) (->verdict false (error :missing input states))
      :else nil))); continue

(defn- step
  [machine input states]
  (let [results (into [] (comp (map :pred) (map #(judge % (first input)))) states)
        matches (keep-indexed #(when (holds? (get results %1)) %2) states)]
    (next-states matches (:nodes machine))))

(defn- traverse
  "traverse the state machine step by step checking if the input given fulfills
  the any of the current sequence of states"
  [machine input states]
  ;(Thread/sleep 10000)
  (if-let [todo (not-empty (step machine input states))]
    (if-let [result (stop? todo input)] result
      (recur machine (rest input) todo))
    (->verdict false (error :mismatch input states))))
    ;{:match false, :msg (str "nothing expected, instead got: " input)}))

(defn exec
  "compares the provided regular expression to the given input. returns a hash-map
  with :match and :msg as the verdict of the match and an error message if the match
  was not sucessfull."
  [auto input]
  (let [machine (cat auto END)
        starts  (vals (peep (get-in machine [:nodes (:fid machine)])
                            (:nodes machine)))]
    (traverse machine input starts)))

(def foo (cat (rep* string?) (and list? vector?) map?))
(exec foo '("hello" (1 2) "world"))

;; (defn- ->viewer
;;   [coll]
;;   (clojure.walk/postwalk
;;     #(cond (record? %) (into {} %)
;;            (fn? %)     (str %)
;;            :else %)     coll))

;; (->viewer (cat foo END))
