(ns probable-lamp.core)

; Represents an NFA state plus zero or one or two arrows exiting
(def END :end) ; no arrows out matching state
(def SPLIT :split); no arrows out matching state
(def LITERAL :literal)

; HACK there be dragons !!
(defn- mk-id [& objs] (hash #()))

(defn- state
  ([checker] (state checker nil nil LITERAL))
  ([checker out out1 flag] {:id (mk-id checker out out1 flag)
                            :type flag, :checker checker, :out out, :out1 out1}))

(defn- patch
  [stat out-id]
  (cond
    (= SPLIT (:type stat)) [(:id stat) (assoc stat :out1 out-id)]
    (nil? (:out stat)) [(:id stat) (assoc stat :out out-id)]
    :default [(:id stat) stat]))

; A partially built NFA without the matching state filled in.
; start is the id of the start state
; content is a hash-map of id-state of all the states in this automaton
(defn- automaton
  ([stat] {:start (:id stat) :content {(:id stat) stat}})
  ([start-id content] {:start start-id :content content}))

(defn cat
  ([auto1 auto2]
   (cond
     (and (fn? auto1) (fn? auto2)) (cat (automaton (state auto1))
                                        (automaton (state auto2)))
     (fn? auto1) (cat (automaton (state auto1)) auto2)
     (fn? auto2) (cat auto1 (automaton (state auto2)))
     :default (let [new-states (into (hash-map) (map patch (vals (:content auto1))
                                                     (repeat (:start auto2))))]
                (assoc auto1 :content (merge new-states (:content auto2))))))
  ([auto1 auto2 & more-autos]
   (reduce cat (cat auto1 auto2) more-autos)))

(defn alt
  ([auto1 auto2]
   (cond
     (and (fn? auto1) (fn? auto2)) (alt (automaton (state auto1))
                                        (automaton (state auto2)))
     (fn? auto1) (alt (automaton (state auto1)) auto2)
     (fn? auto2) (alt auto1 (automaton (state auto2)))
     :default (let [split-st (state nil (:start auto1) (:start auto2) SPLIT)]
                (automaton (:id split-st) (merge (:content auto1)
                                                 {(:id split-st) split-st}
                                                 (:content auto2))))))
  ([auto1 auto2 & more-autos]
   (reduce alt (alt auto1 auto2) more-autos)))


(defn opt
  [automat]
  (if (fn? automat) (opt (automaton (state automat)))
    (let [split-st (state nil (:start automat) nil SPLIT)]
      (automaton (:id split-st) (merge (:content automat)
                                       {(:id split-st) split-st})))))

(defn rep*
  [automat]
  (if (fn? automat) (rep* (automaton (state automat)))
    (let [split-st (state nil (:start automat) nil SPLIT)]
      (automaton (:id split-st) (merge (into (hash-map) (map patch (vals (:content automat))
                                                             (repeat (:id split-st))))
                                       {(:id split-st) split-st})))))

(defn rep+
  [automat]
  (if (fn? automat) (rep+ (automaton (state automat)))
    (let [split-st (state nil (:start automat) nil SPLIT)]
      (automaton (:start automat) (merge (into (hash-map) (map patch (vals (:content automat))
                                                               (repeat (:id split-st))))
                                         {(:id split-st) split-st})))))

(defn exec
  [automat]
  (let [end      (automaton (state nil nil nil END))
        full-mat (cat automat end)]
    nil))
(comment TODOOOOOOOOOOOO)


(cat string? list? vector? map?)
(alt string? list?)

(cat (rep+ string?) map?)
