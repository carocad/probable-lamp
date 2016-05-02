(ns kangaroo.reporter
  (:require [clojure.string :as string]
            [kangaroo.core  :as seql]
            [kangaroo.rules :as rule]))

(def ^:private one? #(= 1 (count %)))

(defn- no-end
  [error]
  (if (and (= :mismatch (:type error))
           (one? (:states error))
           (= seql/END (first (:states error))))
    (dissoc error :states)
    error))

(defn- trim
  "trim deply nested error objects"
  [error]
  (if (and (nil? (:states error)) (some-> (:subex error) (one?)))
    (first (:subex error))
    error))

(defn- collapse
  "collapse a sequence of subex error-objects such that 'similar' errors
  are merged"
  [error]
  (if-not (:subex error) error
    (let [seed   (some #(when (:states %) %) (:subex error))
          others (remove #(= seed %) (:subex error))
          subex  (reduce (fn [ret err]
                           (if (and (nil? (:subex err)) (= (:input (:seed ret)) (:input err)))
                             (assoc-in ret [:seed :states]
                                (concat (->> ret :seed :states) (:states err)))
                             (assoc ret :more (conj (:more ret) err))))
                         {:seed seed :more []}
                         others)]
      (assoc error :subex (cons (:seed subex) (:more subex))))))

(defn- simplify
  "takes an error instance and returns another one without redundant or
  unnecessary information"
  [error]
  (clojure.walk/postwalk collapse
    (clojure.walk/postwalk trim
      (clojure.walk/postwalk no-end error))))

(defn- mcd
  "minimum commom denominator of two or more elements, e.g: [1 2], 1 => 1"
  [expresions]
  (comment TODO))

(defn report
  [error]
  (let [short-error (simplify error)
        input  (with-out-str (pr (:input short-error)))
        stte   (some->> (:states short-error) (map :name) (string/join "\n"))
        suberr (some->> (:subex short-error) (map report) (into [])
                        (string/join "\n"))]
    (if-not (:states error) (string/join "\n" (map report (:subex error)))
      (str "Error processing: " input "\n"
           (when stte (str "Expecting any of: " stte "\n"))
           (if-not (and (not stte) suberr) suberr
             (str "Expecting any of: " suberr))))))

(defn- ->viewer
  [coll]
  (clojure.walk/postwalk
    #(cond (record? %) (into {} %)
           (fn? %)     (str %)
           :else %)     coll))

(->viewer (simplify (seql/exec rule/binding-map
                               '({"a" :a "d" :d}))))

(println (report (simplify (seql/exec rule/binding-map
                             '({"a" :a "d" :d})))))

;;NOTE: minimum size of an exception that I have been able to build
;; (throw (new Throwable "fridge door open"))

