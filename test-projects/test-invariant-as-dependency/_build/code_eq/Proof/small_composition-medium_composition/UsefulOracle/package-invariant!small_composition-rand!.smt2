
;; 

;; base declarations:

(set-logic ALL)
(declare-sort Bits_n
              0)
(declare-const <0_n>
               Bits_n)
(declare-const <1_n>
               Bits_n)
(assert (not (= <1_n>
                <0_n>)))
(declare-datatypes ((Maybe 1))
                   ((par (T)
                         ((mk-some (maybe-get T))
                          (mk-none)))))
(declare-datatypes ((ReturnValue 1))
                   ((par (T)
                         ((mk-return-value (return-value T))
                          (mk-abort)))))
(declare-datatypes ((Tuple1 1))
                   ((par (T1)
                         ((mk-tuple1 (el1-1 T1))))))
(declare-datatypes ((Tuple2 2))
                   ((par (T1 T2)
                         ((mk-tuple2 (el2-1 T1)
                                     (el2-2 T2))))))
(declare-datatypes ((Tuple3 3))
                   ((par (T1 T2
                             T3)
                         ((mk-tuple3 (el3-1 T1)
                                     (el3-2 T2)
                                     (el3-3 T3))))))
(declare-datatypes ((Tuple4 4))
                   ((par (T1 T2
                             T3
                             T4)
                         ((mk-tuple4 (el4-1 T1)
                                     (el4-2 T2)
                                     (el4-3 T3)
                                     (el4-4 T4))))))
(declare-datatypes ((Tuple5 5))
                   ((par (T1 T2
                             T3
                             T4
                             T5)
                         ((mk-tuple5 (el5-1 T1)
                                     (el5-2 T2)
                                     (el5-3 T3)
                                     (el5-4 T4)
                                     (el5-5 T5))))))
(declare-datatypes ((Tuple6 6))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6)
                         ((mk-tuple6 (el6-1 T1)
                                     (el6-2 T2)
                                     (el6-3 T3)
                                     (el6-4 T4)
                                     (el6-5 T5)
                                     (el6-6 T6))))))
(declare-datatypes ((Tuple7 7))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7)
                         ((mk-tuple7 (el7-1 T1)
                                     (el7-2 T2)
                                     (el7-3 T3)
                                     (el7-4 T4)
                                     (el7-5 T5)
                                     (el7-6 T6)
                                     (el7-7 T7))))))
(declare-datatypes ((Tuple8 8))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8)
                         ((mk-tuple8 (el8-1 T1)
                                     (el8-2 T2)
                                     (el8-3 T3)
                                     (el8-4 T4)
                                     (el8-5 T5)
                                     (el8-6 T6)
                                     (el8-7 T7)
                                     (el8-8 T8))))))
(declare-datatypes ((Tuple9 9))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9)
                         ((mk-tuple9 (el9-1 T1)
                                     (el9-2 T2)
                                     (el9-3 T3)
                                     (el9-4 T4)
                                     (el9-5 T5)
                                     (el9-6 T6)
                                     (el9-7 T7)
                                     (el9-8 T8)
                                     (el9-9 T9))))))
(declare-datatypes ((Tuple10 10))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10)
                         ((mk-tuple10 (el10-1 T1)
                                      (el10-2 T2)
                                      (el10-3 T3)
                                      (el10-4 T4)
                                      (el10-5 T5)
                                      (el10-6 T6)
                                      (el10-7 T7)
                                      (el10-8 T8)
                                      (el10-9 T9)
                                      (el10-10 T10))))))
(declare-datatypes ((Tuple11 11))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11)
                         ((mk-tuple11 (el11-1 T1)
                                      (el11-2 T2)
                                      (el11-3 T3)
                                      (el11-4 T4)
                                      (el11-5 T5)
                                      (el11-6 T6)
                                      (el11-7 T7)
                                      (el11-8 T8)
                                      (el11-9 T9)
                                      (el11-10 T10)
                                      (el11-11 T11))))))
(declare-datatypes ((Tuple12 12))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12)
                         ((mk-tuple12 (el12-1 T1)
                                      (el12-2 T2)
                                      (el12-3 T3)
                                      (el12-4 T4)
                                      (el12-5 T5)
                                      (el12-6 T6)
                                      (el12-7 T7)
                                      (el12-8 T8)
                                      (el12-9 T9)
                                      (el12-10 T10)
                                      (el12-11 T11)
                                      (el12-12 T12))))))
(declare-datatypes ((Tuple13 13))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13)
                         ((mk-tuple13 (el13-1 T1)
                                      (el13-2 T2)
                                      (el13-3 T3)
                                      (el13-4 T4)
                                      (el13-5 T5)
                                      (el13-6 T6)
                                      (el13-7 T7)
                                      (el13-8 T8)
                                      (el13-9 T9)
                                      (el13-10 T10)
                                      (el13-11 T11)
                                      (el13-12 T12)
                                      (el13-13 T13))))))
(declare-datatypes ((Tuple14 14))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14)
                         ((mk-tuple14 (el14-1 T1)
                                      (el14-2 T2)
                                      (el14-3 T3)
                                      (el14-4 T4)
                                      (el14-5 T5)
                                      (el14-6 T6)
                                      (el14-7 T7)
                                      (el14-8 T8)
                                      (el14-9 T9)
                                      (el14-10 T10)
                                      (el14-11 T11)
                                      (el14-12 T12)
                                      (el14-13 T13)
                                      (el14-14 T14))))))
(declare-datatypes ((Tuple15 15))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15)
                         ((mk-tuple15 (el15-1 T1)
                                      (el15-2 T2)
                                      (el15-3 T3)
                                      (el15-4 T4)
                                      (el15-5 T5)
                                      (el15-6 T6)
                                      (el15-7 T7)
                                      (el15-8 T8)
                                      (el15-9 T9)
                                      (el15-10 T10)
                                      (el15-11 T11)
                                      (el15-12 T12)
                                      (el15-13 T13)
                                      (el15-14 T14)
                                      (el15-15 T15))))))
(declare-datatypes ((Tuple16 16))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16)
                         ((mk-tuple16 (el16-1 T1)
                                      (el16-2 T2)
                                      (el16-3 T3)
                                      (el16-4 T4)
                                      (el16-5 T5)
                                      (el16-6 T6)
                                      (el16-7 T7)
                                      (el16-8 T8)
                                      (el16-9 T9)
                                      (el16-10 T10)
                                      (el16-11 T11)
                                      (el16-12 T12)
                                      (el16-13 T13)
                                      (el16-14 T14)
                                      (el16-15 T15)
                                      (el16-16 T16))))))
(declare-datatypes ((Tuple17 17))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17)
                         ((mk-tuple17 (el17-1 T1)
                                      (el17-2 T2)
                                      (el17-3 T3)
                                      (el17-4 T4)
                                      (el17-5 T5)
                                      (el17-6 T6)
                                      (el17-7 T7)
                                      (el17-8 T8)
                                      (el17-9 T9)
                                      (el17-10 T10)
                                      (el17-11 T11)
                                      (el17-12 T12)
                                      (el17-13 T13)
                                      (el17-14 T14)
                                      (el17-15 T15)
                                      (el17-16 T16)
                                      (el17-17 T17))))))
(declare-datatypes ((Tuple18 18))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18)
                         ((mk-tuple18 (el18-1 T1)
                                      (el18-2 T2)
                                      (el18-3 T3)
                                      (el18-4 T4)
                                      (el18-5 T5)
                                      (el18-6 T6)
                                      (el18-7 T7)
                                      (el18-8 T8)
                                      (el18-9 T9)
                                      (el18-10 T10)
                                      (el18-11 T11)
                                      (el18-12 T12)
                                      (el18-13 T13)
                                      (el18-14 T14)
                                      (el18-15 T15)
                                      (el18-16 T16)
                                      (el18-17 T17)
                                      (el18-18 T18))))))
(declare-datatypes ((Tuple19 19))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19)
                         ((mk-tuple19 (el19-1 T1)
                                      (el19-2 T2)
                                      (el19-3 T3)
                                      (el19-4 T4)
                                      (el19-5 T5)
                                      (el19-6 T6)
                                      (el19-7 T7)
                                      (el19-8 T8)
                                      (el19-9 T9)
                                      (el19-10 T10)
                                      (el19-11 T11)
                                      (el19-12 T12)
                                      (el19-13 T13)
                                      (el19-14 T14)
                                      (el19-15 T15)
                                      (el19-16 T16)
                                      (el19-17 T17)
                                      (el19-18 T18)
                                      (el19-19 T19))))))
(declare-datatypes ((Tuple20 20))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20)
                         ((mk-tuple20 (el20-1 T1)
                                      (el20-2 T2)
                                      (el20-3 T3)
                                      (el20-4 T4)
                                      (el20-5 T5)
                                      (el20-6 T6)
                                      (el20-7 T7)
                                      (el20-8 T8)
                                      (el20-9 T9)
                                      (el20-10 T10)
                                      (el20-11 T11)
                                      (el20-12 T12)
                                      (el20-13 T13)
                                      (el20-14 T14)
                                      (el20-15 T15)
                                      (el20-16 T16)
                                      (el20-17 T17)
                                      (el20-18 T18)
                                      (el20-19 T19)
                                      (el20-20 T20))))))
(declare-datatypes ((Tuple21 21))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21)
                         ((mk-tuple21 (el21-1 T1)
                                      (el21-2 T2)
                                      (el21-3 T3)
                                      (el21-4 T4)
                                      (el21-5 T5)
                                      (el21-6 T6)
                                      (el21-7 T7)
                                      (el21-8 T8)
                                      (el21-9 T9)
                                      (el21-10 T10)
                                      (el21-11 T11)
                                      (el21-12 T12)
                                      (el21-13 T13)
                                      (el21-14 T14)
                                      (el21-15 T15)
                                      (el21-16 T16)
                                      (el21-17 T17)
                                      (el21-18 T18)
                                      (el21-19 T19)
                                      (el21-20 T20)
                                      (el21-21 T21))))))
(declare-datatypes ((Tuple22 22))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22)
                         ((mk-tuple22 (el22-1 T1)
                                      (el22-2 T2)
                                      (el22-3 T3)
                                      (el22-4 T4)
                                      (el22-5 T5)
                                      (el22-6 T6)
                                      (el22-7 T7)
                                      (el22-8 T8)
                                      (el22-9 T9)
                                      (el22-10 T10)
                                      (el22-11 T11)
                                      (el22-12 T12)
                                      (el22-13 T13)
                                      (el22-14 T14)
                                      (el22-15 T15)
                                      (el22-16 T16)
                                      (el22-17 T17)
                                      (el22-18 T18)
                                      (el22-19 T19)
                                      (el22-20 T20)
                                      (el22-21 T21)
                                      (el22-22 T22))))))
(declare-datatypes ((Tuple23 23))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23)
                         ((mk-tuple23 (el23-1 T1)
                                      (el23-2 T2)
                                      (el23-3 T3)
                                      (el23-4 T4)
                                      (el23-5 T5)
                                      (el23-6 T6)
                                      (el23-7 T7)
                                      (el23-8 T8)
                                      (el23-9 T9)
                                      (el23-10 T10)
                                      (el23-11 T11)
                                      (el23-12 T12)
                                      (el23-13 T13)
                                      (el23-14 T14)
                                      (el23-15 T15)
                                      (el23-16 T16)
                                      (el23-17 T17)
                                      (el23-18 T18)
                                      (el23-19 T19)
                                      (el23-20 T20)
                                      (el23-21 T21)
                                      (el23-22 T22)
                                      (el23-23 T23))))))
(declare-datatypes ((Tuple24 24))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24)
                         ((mk-tuple24 (el24-1 T1)
                                      (el24-2 T2)
                                      (el24-3 T3)
                                      (el24-4 T4)
                                      (el24-5 T5)
                                      (el24-6 T6)
                                      (el24-7 T7)
                                      (el24-8 T8)
                                      (el24-9 T9)
                                      (el24-10 T10)
                                      (el24-11 T11)
                                      (el24-12 T12)
                                      (el24-13 T13)
                                      (el24-14 T14)
                                      (el24-15 T15)
                                      (el24-16 T16)
                                      (el24-17 T17)
                                      (el24-18 T18)
                                      (el24-19 T19)
                                      (el24-20 T20)
                                      (el24-21 T21)
                                      (el24-22 T22)
                                      (el24-23 T23)
                                      (el24-24 T24))))))
(declare-datatypes ((Tuple25 25))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24
                             T25)
                         ((mk-tuple25 (el25-1 T1)
                                      (el25-2 T2)
                                      (el25-3 T3)
                                      (el25-4 T4)
                                      (el25-5 T5)
                                      (el25-6 T6)
                                      (el25-7 T7)
                                      (el25-8 T8)
                                      (el25-9 T9)
                                      (el25-10 T10)
                                      (el25-11 T11)
                                      (el25-12 T12)
                                      (el25-13 T13)
                                      (el25-14 T14)
                                      (el25-15 T15)
                                      (el25-16 T16)
                                      (el25-17 T17)
                                      (el25-18 T18)
                                      (el25-19 T19)
                                      (el25-20 T20)
                                      (el25-21 T21)
                                      (el25-22 T22)
                                      (el25-23 T23)
                                      (el25-24 T24)
                                      (el25-25 T25))))))
(declare-datatypes ((Tuple26 26))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24
                             T25
                             T26)
                         ((mk-tuple26 (el26-1 T1)
                                      (el26-2 T2)
                                      (el26-3 T3)
                                      (el26-4 T4)
                                      (el26-5 T5)
                                      (el26-6 T6)
                                      (el26-7 T7)
                                      (el26-8 T8)
                                      (el26-9 T9)
                                      (el26-10 T10)
                                      (el26-11 T11)
                                      (el26-12 T12)
                                      (el26-13 T13)
                                      (el26-14 T14)
                                      (el26-15 T15)
                                      (el26-16 T16)
                                      (el26-17 T17)
                                      (el26-18 T18)
                                      (el26-19 T19)
                                      (el26-20 T20)
                                      (el26-21 T21)
                                      (el26-22 T22)
                                      (el26-23 T23)
                                      (el26-24 T24)
                                      (el26-25 T25)
                                      (el26-26 T26))))))
(declare-datatypes ((Tuple27 27))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24
                             T25
                             T26
                             T27)
                         ((mk-tuple27 (el27-1 T1)
                                      (el27-2 T2)
                                      (el27-3 T3)
                                      (el27-4 T4)
                                      (el27-5 T5)
                                      (el27-6 T6)
                                      (el27-7 T7)
                                      (el27-8 T8)
                                      (el27-9 T9)
                                      (el27-10 T10)
                                      (el27-11 T11)
                                      (el27-12 T12)
                                      (el27-13 T13)
                                      (el27-14 T14)
                                      (el27-15 T15)
                                      (el27-16 T16)
                                      (el27-17 T17)
                                      (el27-18 T18)
                                      (el27-19 T19)
                                      (el27-20 T20)
                                      (el27-21 T21)
                                      (el27-22 T22)
                                      (el27-23 T23)
                                      (el27-24 T24)
                                      (el27-25 T25)
                                      (el27-26 T26)
                                      (el27-27 T27))))))
(declare-datatypes ((Tuple28 28))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24
                             T25
                             T26
                             T27
                             T28)
                         ((mk-tuple28 (el28-1 T1)
                                      (el28-2 T2)
                                      (el28-3 T3)
                                      (el28-4 T4)
                                      (el28-5 T5)
                                      (el28-6 T6)
                                      (el28-7 T7)
                                      (el28-8 T8)
                                      (el28-9 T9)
                                      (el28-10 T10)
                                      (el28-11 T11)
                                      (el28-12 T12)
                                      (el28-13 T13)
                                      (el28-14 T14)
                                      (el28-15 T15)
                                      (el28-16 T16)
                                      (el28-17 T17)
                                      (el28-18 T18)
                                      (el28-19 T19)
                                      (el28-20 T20)
                                      (el28-21 T21)
                                      (el28-22 T22)
                                      (el28-23 T23)
                                      (el28-24 T24)
                                      (el28-25 T25)
                                      (el28-26 T26)
                                      (el28-27 T27)
                                      (el28-28 T28))))))
(declare-datatypes ((Tuple29 29))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24
                             T25
                             T26
                             T27
                             T28
                             T29)
                         ((mk-tuple29 (el29-1 T1)
                                      (el29-2 T2)
                                      (el29-3 T3)
                                      (el29-4 T4)
                                      (el29-5 T5)
                                      (el29-6 T6)
                                      (el29-7 T7)
                                      (el29-8 T8)
                                      (el29-9 T9)
                                      (el29-10 T10)
                                      (el29-11 T11)
                                      (el29-12 T12)
                                      (el29-13 T13)
                                      (el29-14 T14)
                                      (el29-15 T15)
                                      (el29-16 T16)
                                      (el29-17 T17)
                                      (el29-18 T18)
                                      (el29-19 T19)
                                      (el29-20 T20)
                                      (el29-21 T21)
                                      (el29-22 T22)
                                      (el29-23 T23)
                                      (el29-24 T24)
                                      (el29-25 T25)
                                      (el29-26 T26)
                                      (el29-27 T27)
                                      (el29-28 T28)
                                      (el29-29 T29))))))
(declare-datatypes ((Tuple30 30))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24
                             T25
                             T26
                             T27
                             T28
                             T29
                             T30)
                         ((mk-tuple30 (el30-1 T1)
                                      (el30-2 T2)
                                      (el30-3 T3)
                                      (el30-4 T4)
                                      (el30-5 T5)
                                      (el30-6 T6)
                                      (el30-7 T7)
                                      (el30-8 T8)
                                      (el30-9 T9)
                                      (el30-10 T10)
                                      (el30-11 T11)
                                      (el30-12 T12)
                                      (el30-13 T13)
                                      (el30-14 T14)
                                      (el30-15 T15)
                                      (el30-16 T16)
                                      (el30-17 T17)
                                      (el30-18 T18)
                                      (el30-19 T19)
                                      (el30-20 T20)
                                      (el30-21 T21)
                                      (el30-22 T22)
                                      (el30-23 T23)
                                      (el30-24 T24)
                                      (el30-25 T25)
                                      (el30-26 T26)
                                      (el30-27 T27)
                                      (el30-28 T28)
                                      (el30-29 T29)
                                      (el30-30 T30))))))
(declare-datatypes ((Tuple31 31))
                   ((par (T1 T2
                             T3
                             T4
                             T5
                             T6
                             T7
                             T8
                             T9
                             T10
                             T11
                             T12
                             T13
                             T14
                             T15
                             T16
                             T17
                             T18
                             T19
                             T20
                             T21
                             T22
                             T23
                             T24
                             T25
                             T26
                             T27
                             T28
                             T29
                             T30
                             T31)
                         ((mk-tuple31 (el31-1 T1)
                                      (el31-2 T2)
                                      (el31-3 T3)
                                      (el31-4 T4)
                                      (el31-5 T5)
                                      (el31-6 T6)
                                      (el31-7 T7)
                                      (el31-8 T8)
                                      (el31-9 T9)
                                      (el31-10 T10)
                                      (el31-11 T11)
                                      (el31-12 T12)
                                      (el31-13 T13)
                                      (el31-14 T14)
                                      (el31-15 T15)
                                      (el31-16 T16)
                                      (el31-17 T17)
                                      (el31-18 T18)
                                      (el31-19 T19)
                                      (el31-20 T20)
                                      (el31-21 T21)
                                      (el31-22 T22)
                                      (el31-23 T23)
                                      (el31-24 T24)
                                      (el31-25 T25)
                                      (el31-26 T26)
                                      (el31-27 T27)
                                      (el31-28 T28)
                                      (el31-29 T29)
                                      (el31-30 T30)
                                      (el31-31 T31))))))
(declare-datatype Empty
                  ((mk-empty)))
(declare-datatype SampleId
                  ((sample-id (sample-pkg-name String)
                              (sample-oracle-name String)
                              (sample-name String))))
;; 

;; theorem param funcs:

(declare-fun <<func-f>>
             (Int)
             Int)
;; 

;; game definitions:

(declare-fun __sample-rand-small_composition-Bits_n
             (SampleId Int)
             Bits_n)
(declare-fun __sample-rand-medium_composition-Bits_n
             (SampleId Int)
             Bits_n)
(declare-datatype <PackageConsts_Rand>
                  ((<mk-pkg-consts-Rand> (<pkg-consts-Rand-n> Int))))
(declare-datatype <PackageConsts_Fwd>
                  ((<mk-pkg-consts-Fwd> (<pkg-consts-Fwd-n> Int))))
(declare-datatype <PackageState_Rand_<$<!n!>$>>
                  ((<mk-pkg-state-Rand-<$<!n!>$>> (<pkg-state-Rand-<$<!n!>$>-ctr> Int))))
(declare-datatype <PackageState_Fwd_<$<!n!>$>>
                  ((<mk-pkg-state-Fwd-<$<!n!>$>> (<pkg-state-Fwd-<$<!n!>$>-ctr> Int))))
(declare-datatype <TheoremConsts_Proof>
                  ((<mk-theorem-consts-Proof> (<theorem-consts-Proof-n> Int))))
(declare-datatype <GameConsts_SmallComposition>
                  ((<mk-game-consts-SmallComposition> (<game-consts-SmallComposition-n> Int))))
(declare-datatype <GameConsts_MediumComposition>
                  ((<mk-game-consts-MediumComposition> (<game-consts-MediumComposition-n> Int))))
(declare-datatype <GameState_SmallComposition_<$<!n!>$>>
                  ((<mk-game-SmallComposition-<$<!n!>$>> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> <PackageState_Rand_<$<!n!>$>>)
                                                         (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> Int)
                                                         (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> Int))))
(declare-datatype <GameState_MediumComposition_<$<!n!>$>>
                  ((<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <PackageState_Rand_<$<!n!>$>>)
                                                          (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <PackageState_Fwd_<$<!n!>$>>)
                                                          (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> Int)
                                                          (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> Int))))
(define-fun <gameconsts-Proof-small_composition>
            ((<theorem-consts> <TheoremConsts_Proof>))
            <GameConsts_SmallComposition>
            (let ((n (<theorem-consts-Proof-n> <theorem-consts>)))
                 (<mk-game-consts-SmallComposition> n)))
(define-fun <gameconsts-Proof-medium_composition>
            ((<theorem-consts> <TheoremConsts_Proof>))
            <GameConsts_MediumComposition>
            (let ((n (<theorem-consts-Proof-n> <theorem-consts>)))
                 (<mk-game-consts-MediumComposition> n)))
(define-fun <pkgconsts-SmallComposition-rand>
            ((<game-consts> <GameConsts_SmallComposition>))
            <PackageConsts_Rand>
            (let ((n (<game-consts-SmallComposition-n> <game-consts>)))
                 (<mk-pkg-consts-Rand> n)))
(define-fun <pkgconsts-MediumComposition-rand>
            ((<game-consts> <GameConsts_MediumComposition>))
            <PackageConsts_Rand>
            (let ((n (<game-consts-MediumComposition-n> <game-consts>)))
                 (<mk-pkg-consts-Rand> n)))
(define-fun <pkgconsts-MediumComposition-fwd>
            ((<game-consts> <GameConsts_MediumComposition>))
            <PackageConsts_Fwd>
            (let ((n (<game-consts-MediumComposition-n> <game-consts>)))
                 (<mk-pkg-consts-Fwd> n)))
(declare-datatype <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>
                  ((<mk-oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle> (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-game-state> <GameState_SmallComposition_<$<!n!>$>>)
                                                                                              (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> (ReturnValue (Tuple2 Int
                                                                                                                                                                                                                 Bits_n))))))
(declare-datatype <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UselessOracle>
                  ((<mk-oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle> (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle-game-state> <GameState_SmallComposition_<$<!n!>$>>)
                                                                                               (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle-return-value-or-abort> (ReturnValue Int)))))
(declare-datatype <OracleReturn_MediumComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>
                  ((<mk-oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle> (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-game-state> <GameState_MediumComposition_<$<!n!>$>>)
                                                                                               (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> (ReturnValue (Tuple2 Int
                                                                                                                                                                                                                   Bits_n))))))
(declare-datatype <OracleReturn_MediumComposition_<$<!n!>$>_Rand_<$<!n!>$>_UselessOracle>
                  ((<mk-oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle> (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle-game-state> <GameState_MediumComposition_<$<!n!>$>>)
                                                                                                (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle-return-value-or-abort> (ReturnValue Int)))))
(declare-datatype <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>
                  ((<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle> (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-game-state> <GameState_MediumComposition_<$<!n!>$>>)
                                                                                              (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-return-value-or-abort> (ReturnValue (Tuple2 Int
                                                                                                                                                                                                                 Bits_n))))))
(declare-datatype <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UselessOracle>
                  ((<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UselessOracle> (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UselessOracle-game-state> <GameState_MediumComposition_<$<!n!>$>>)
                                                                                               (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UselessOracle-return-value-or-abort> (ReturnValue Int)))))
(define-fun <oracle-SmallComposition-small_composition-Rand-rand-<$<!f!><!n!>$>-UsefulOracle>
            ((<game-state> <GameState_SmallComposition_<$<!n!>$>>)
             (<game-consts> <GameConsts_SmallComposition>))
            <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>
            (let ((ctr (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> <game-state>))))
                 (let ((n (<pkg-consts-Rand-n> (<pkgconsts-SmallComposition-rand> <game-consts>))))
                      (let ((ctr (+ ctr
                                    1)))
                           (let ((rand (__sample-rand-small_composition-Bits_n (sample-id "rand"
                                                                                          "UsefulOracle"
                                                                                          "samplepoint")
                                                                               (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>))))
                                (let ((<game-state> (<mk-game-SmallComposition-<$<!n!>$>> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                          (+ 1
                                                                                             (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>))
                                                                                          (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))))
                                     (<mk-oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle> (<mk-game-SmallComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> ctr)
                                                                                                                                                      (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                                                                                      (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))
                                                                                                                (mk-return-value (mk-tuple2 ctr
                                                                                                                                            rand)))))))))
(define-fun <oracle-SmallComposition-small_composition-Rand-rand-<$<!f!><!n!>$>-UselessOracle>
            ((<game-state> <GameState_SmallComposition_<$<!n!>$>>)
             (<game-consts> <GameConsts_SmallComposition>)
             (x Int))
            <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UselessOracle>
            (let ((ctr (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> <game-state>))))
                 (let ((n (<pkg-consts-Rand-n> (<pkgconsts-SmallComposition-rand> <game-consts>))))
                      (ite (= x
                              1)
                           (let ((rand (__sample-rand-small_composition-Bits_n (sample-id "rand"
                                                                                          "UselessOracle"
                                                                                          "1")
                                                                               (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))))
                                (let ((<game-state> (<mk-game-SmallComposition-<$<!n!>$>> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                          (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                          (+ 1
                                                                                             (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>)))))
                                     (<mk-oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle> (<mk-game-SmallComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> ctr)
                                                                                                                                                       (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                                                                                       (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))
                                                                                                                 (mk-return-value 1))))
                           (let ((<game-state> (<mk-game-SmallComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> ctr)
                                                                                     (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                     (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))))
                                (<mk-oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle> <game-state>
                                                                                                            (as mk-abort
                                                                                                                (ReturnValue Int))))))))
(define-fun <oracle-MediumComposition-medium_composition-Rand-rand-<$<!f!><!n!>$>-UsefulOracle>
            ((<game-state> <GameState_MediumComposition_<$<!n!>$>>)
             (<game-consts> <GameConsts_MediumComposition>))
            <OracleReturn_MediumComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>
            (let ((ctr (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>))))
                 (let ((n (<pkg-consts-Rand-n> (<pkgconsts-MediumComposition-rand> <game-consts>))))
                      (let ((ctr (+ ctr
                                    1)))
                           (let ((rand (__sample-rand-medium_composition-Bits_n (sample-id "rand"
                                                                                           "UsefulOracle"
                                                                                           "samplepoint")
                                                                                (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>))))
                                (let ((<game-state> (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                           (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <game-state>)
                                                                                           (+ 1
                                                                                              (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>))
                                                                                           (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))))
                                     (<mk-oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle> (<mk-game-MediumComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> ctr)
                                                                                                                                                        (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <game-state>)
                                                                                                                                                        (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                                                                                        (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))
                                                                                                                 (mk-return-value (mk-tuple2 ctr
                                                                                                                                             rand)))))))))
(define-fun <oracle-MediumComposition-medium_composition-Rand-rand-<$<!f!><!n!>$>-UselessOracle>
            ((<game-state> <GameState_MediumComposition_<$<!n!>$>>)
             (<game-consts> <GameConsts_MediumComposition>)
             (x Int))
            <OracleReturn_MediumComposition_<$<!n!>$>_Rand_<$<!n!>$>_UselessOracle>
            (let ((ctr (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>))))
                 (let ((n (<pkg-consts-Rand-n> (<pkgconsts-MediumComposition-rand> <game-consts>))))
                      (ite (= x
                              1)
                           (let ((rand (__sample-rand-medium_composition-Bits_n (sample-id "rand"
                                                                                           "UselessOracle"
                                                                                           "1")
                                                                                (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))))
                                (let ((<game-state> (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                           (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <game-state>)
                                                                                           (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                           (+ 1
                                                                                              (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>)))))
                                     (<mk-oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle> (<mk-game-MediumComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> ctr)
                                                                                                                                                         (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <game-state>)
                                                                                                                                                         (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                                                                                         (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))
                                                                                                                  (mk-return-value 1))))
                           (let ((<game-state> (<mk-game-MediumComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> ctr)
                                                                                      (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <game-state>)
                                                                                      (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                      (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))))
                                (<mk-oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UselessOracle> <game-state>
                                                                                                             (as mk-abort
                                                                                                                 (ReturnValue Int))))))))
(define-fun <oracle-MediumComposition-medium_composition-Fwd-fwd-<$<!n!>$>-UsefulOracle>
            ((<game-state> <GameState_MediumComposition_<$<!n!>$>>)
             (<game-consts> <GameConsts_MediumComposition>))
            <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>
            (let ((ctr (<pkg-state-Fwd-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <game-state>))))
                 (let ((n (<pkg-consts-Fwd-n> (<pkgconsts-MediumComposition-fwd> <game-consts>))))
                      (let ((__ret (<oracle-MediumComposition-medium_composition-Rand-rand-<$<!f!><!n!>$>-UsefulOracle> <game-state>
                                                                                                                        <game-consts>)))
                           (ite (= (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> __ret)
                                   (as mk-abort
                                       (ReturnValue (Tuple2 Int
                                                            Bits_n))))
                                (let ((<game-state> (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-game-state> __ret)))
                                     (<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle> (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                                                                                       (<mk-pkg-state-Fwd-<$<!n!>$>> ctr)
                                                                                                                                                       (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                                                                                       (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))
                                                                                                                (as mk-abort
                                                                                                                    (ReturnValue (Tuple2 Int
                                                                                                                                         Bits_n)))))
                                (let ((<game-state> (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-game-state> __ret))
                                      (y (return-value (<oracle-return-MediumComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> __ret))))
                                     (<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle> (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                                                                                       (<mk-pkg-state-Fwd-<$<!n!>$>> ctr)
                                                                                                                                                       (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                                                                                       (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))
                                                                                                                (mk-return-value y))))))))
(define-fun <oracle-MediumComposition-medium_composition-Fwd-fwd-<$<!n!>$>-UselessOracle>
            ((<game-state> <GameState_MediumComposition_<$<!n!>$>>)
             (<game-consts> <GameConsts_MediumComposition>)
             (x Int))
            <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UselessOracle>
            (let ((ctr (<pkg-state-Fwd-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <game-state>))))
                 (let ((n (<pkg-consts-Fwd-n> (<pkgconsts-MediumComposition-fwd> <game-consts>))))
                      (ite (= x
                              1)
                           (<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UselessOracle> (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                                                                              (<mk-pkg-state-Fwd-<$<!n!>$>> ctr)
                                                                                                                                              (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                                                                              (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))
                                                                                                       (mk-return-value 1))
                           (let ((<game-state> (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <game-state>)
                                                                                      (<mk-pkg-state-Fwd-<$<!n!>$>> ctr)
                                                                                      (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <game-state>)
                                                                                      (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <game-state>))))
                                (<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UselessOracle> <game-state>
                                                                                                            (as mk-abort
                                                                                                                (ReturnValue Int))))))))
(declare-const <<game-state-small_composition-old>>
               <GameState_SmallComposition_<$<!n!>$>>)
(declare-const <<game-state-medium_composition-old>>
               <GameState_MediumComposition_<$<!n!>$>>)
(declare-const <<theorem-consts>>
               <TheoremConsts_Proof>)
(define-fun <<game-consts-small_composition>>
            ()
            <GameConsts_SmallComposition>
            (<gameconsts-Proof-small_composition> <<theorem-consts>>))
(define-fun <<game-consts-medium_composition>>
            ()
            <GameConsts_MediumComposition>
            (<gameconsts-Proof-medium_composition> <<theorem-consts>>))
(declare-const <return-small_composition-UsefulOracle>
               <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)
(assert (= <return-small_composition-UsefulOracle>
           (<oracle-SmallComposition-small_composition-Rand-rand-<$<!f!><!n!>$>-UsefulOracle> <<game-state-small_composition-old>>
                                                                                              <<game-consts-small_composition>>)))
(declare-const return-value-small_composition-rand-UsefulOracle
               (ReturnValue (Tuple2 Int
                                    Bits_n)))
(assert (= return-value-small_composition-rand-UsefulOracle
           (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> <return-small_composition-UsefulOracle>)))
(declare-const <return-is-abort-small_composition-rand-UsefulOracle>
               Bool)
(assert (= <return-is-abort-small_composition-rand-UsefulOracle>
           (match return-value-small_composition-rand-UsefulOracle
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))
(declare-const <<game-state-small_composition-new-UsefulOracle>>
               <GameState_SmallComposition_<$<!n!>$>>)
(assert (= <<game-state-small_composition-new-UsefulOracle>>
           (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-game-state> <return-small_composition-UsefulOracle>)))
(declare-const <return-medium_composition-UsefulOracle>
               <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>)
(assert (= <return-medium_composition-UsefulOracle>
           (<oracle-MediumComposition-medium_composition-Fwd-fwd-<$<!n!>$>-UsefulOracle> <<game-state-medium_composition-old>>
                                                                                         <<game-consts-medium_composition>>)))
(declare-const return-value-medium_composition-fwd-UsefulOracle
               (ReturnValue (Tuple2 Int
                                    Bits_n)))
(assert (= return-value-medium_composition-fwd-UsefulOracle
           (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-return-value-or-abort> <return-medium_composition-UsefulOracle>)))
(declare-const <return-is-abort-medium_composition-fwd-UsefulOracle>
               Bool)
(assert (= <return-is-abort-medium_composition-fwd-UsefulOracle>
           (match return-value-medium_composition-fwd-UsefulOracle
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))
(declare-const <<game-state-medium_composition-new-UsefulOracle>>
               <GameState_MediumComposition_<$<!n!>$>>)
(assert (= <<game-state-medium_composition-new-UsefulOracle>>
           (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-game-state> <return-medium_composition-UsefulOracle>)))
(declare-const randctr-small_composition-0
               Int)
(assert (= randctr-small_composition-0
           (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <<game-state-small_composition-old>>)))
(assert (= randctr-small_composition-0
           0))
(declare-const randval-small_composition-0
               Bits_n)
(assert (= randval-small_composition-0
           (__sample-rand-small_composition-Bits_n (sample-id "rand"
                                                              "UsefulOracle"
                                                              "samplepoint")
                                                   (+ 0
                                                      randctr-small_composition-0))))
(declare-const randctr-small_composition-1
               Int)
(assert (= randctr-small_composition-1
           (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <<game-state-small_composition-old>>)))
(assert (= randctr-small_composition-1
           0))
(declare-const randval-small_composition-1
               Bits_n)
(assert (= randval-small_composition-1
           (__sample-rand-small_composition-Bits_n (sample-id "rand"
                                                              "UselessOracle"
                                                              "1")
                                                   (+ 0
                                                      randctr-small_composition-1))))
(declare-const randctr-medium_composition-0
               Int)
(assert (= randctr-medium_composition-0
           (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <<game-state-medium_composition-old>>)))
(assert (= randctr-medium_composition-0
           0))
(declare-const randval-medium_composition-0
               Bits_n)
(assert (= randval-medium_composition-0
           (__sample-rand-medium_composition-Bits_n (sample-id "rand"
                                                               "UsefulOracle"
                                                               "samplepoint")
                                                    (+ 0
                                                       randctr-medium_composition-0))))
(declare-const randctr-medium_composition-1
               Int)
(assert (= randctr-medium_composition-1
           (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <<game-state-medium_composition-old>>)))
(assert (= randctr-medium_composition-1
           0))
(declare-const randval-medium_composition-1
               Bits_n)
(assert (= randval-medium_composition-1
           (__sample-rand-medium_composition-Bits_n (sample-id "rand"
                                                               "UselessOracle"
                                                               "1")
                                                    (+ 0
                                                       randctr-medium_composition-1))))
(define-fun get-rand-ctr-small_composition
            ((sampleid SampleId))
            Int
            (ite (= sampleid
                    (sample-id "rand"
                               "UselessOracle"
                               "1"))
                 (<game-SmallComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <<game-state-small_composition-old>>)
                 (ite (= sampleid
                         (sample-id "rand"
                                    "UsefulOracle"
                                    "samplepoint"))
                      (<game-SmallComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <<game-state-small_composition-old>>)
                      0)))
(define-fun get-rand-ctr-medium_composition
            ((sampleid SampleId))
            Int
            (ite (= sampleid
                    (sample-id "rand"
                               "UselessOracle"
                               "1"))
                 (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <<game-state-medium_composition-old>>)
                 (ite (= sampleid
                         (sample-id "rand"
                                    "UsefulOracle"
                                    "samplepoint"))
                      (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <<game-state-medium_composition-old>>)
                      0)))
(define-fun rand-is-eq
            ((sample-id-left SampleId)
             (sample-id-right SampleId)
             (sample-ctr-left Int)
             (sample-ctr-right Int))
            Bool
            (ite (and (or (= (sample-id "rand"
                                        "UsefulOracle"
                                        "samplepoint")
                             sample-id-left)
                          (= (sample-id "rand"
                                        "UselessOracle"
                                        "1")
                             sample-id-left))
                      (or (= (sample-id "rand"
                                        "UsefulOracle"
                                        "samplepoint")
                             sample-id-right)
                          (= (sample-id "rand"
                                        "UselessOracle"
                                        "1")
                             sample-id-right)))
                 (= (__sample-rand-small_composition-Bits_n sample-id-left
                                                            sample-ctr-left)
                    (__sample-rand-medium_composition-Bits_n sample-id-right
                                                             sample-ctr-right))
                 true))
(declare-const <equal-aborts>
               Bool)
(assert (= <equal-aborts>
           (= (match return-value-small_composition-rand-UsefulOracle
                     (((mk-return-value returnvalue)
                       false)
                      (mk-abort true)))
              (match return-value-medium_composition-fwd-UsefulOracle
                     (((mk-return-value returnvalue)
                       false)
                      (mk-abort true))))))
(declare-const <no-aborts>
               Bool)
(assert (= <no-aborts>
           (and (not (match return-value-small_composition-rand-UsefulOracle
                            (((mk-return-value returnvalue)
                              false)
                             (mk-abort true))))
                (not (match return-value-medium_composition-fwd-UsefulOracle
                            (((mk-return-value returnvalue)
                              false)
                             (mk-abort true)))))))
(declare-const <same-outputs>
               Bool)
(assert (= <same-outputs>
           (= return-value-small_composition-rand-UsefulOracle
              return-value-medium_composition-fwd-UsefulOracle)))
(define-fun <relation-equal-aborts-small_composition-medium_composition-UsefulOracle>
            ((old-state-left <GameState_SmallComposition_<$<!n!>$>>)
             (old-state-right <GameState_MediumComposition_<$<!n!>$>>)
             (return-left <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)
             (return-right <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>))
            Bool
            (let ((return-value-left (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-left))
                  (return-value-right (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-right)))
                 (= ((_ is
                        mk-abort)
                     return-value-left)
                    ((_ is
                        mk-abort)
                     return-value-right))))
(define-fun <relation-left-no-abort-small_composition-medium_composition-UsefulOracle>
            ((old-state-left <GameState_SmallComposition_<$<!n!>$>>)
             (old-state-right <GameState_MediumComposition_<$<!n!>$>>)
             (return-left <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)
             (return-right <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>))
            Bool
            (not ((_ is
                     mk-abort)
                  (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-left))))
(define-fun <relation-right-no-abort-small_composition-medium_composition-UsefulOracle>
            ((old-state-left <GameState_SmallComposition_<$<!n!>$>>)
             (old-state-right <GameState_MediumComposition_<$<!n!>$>>)
             (return-left <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)
             (return-right <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>))
            Bool
            (not ((_ is
                     mk-abort)
                  (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-right))))
(define-fun <relation-no-abort-small_composition-medium_composition-UsefulOracle>
            ((old-state-left <GameState_SmallComposition_<$<!n!>$>>)
             (old-state-right <GameState_MediumComposition_<$<!n!>$>>)
             (return-left <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)
             (return-right <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>))
            Bool
            (and (not ((_ is
                          mk-abort)
                       (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-left)))
                 (not ((_ is
                          mk-abort)
                       (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-right)))))
(define-fun <relation-same-output-small_composition-medium_composition-UsefulOracle>
            ((old-state-left <GameState_SmallComposition_<$<!n!>$>>)
             (old-state-right <GameState_MediumComposition_<$<!n!>$>>)
             (return-left <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)
             (return-right <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle>))
            Bool
            (= (<oracle-return-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-left)
               (<oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle-return-value-or-abort> return-right)))
(define-fun randomness-mapping-UsefulOracle
            ((sample-id-0 SampleId)
             (sample-id-1 SampleId)
             (offset-0 Int)
             (offset-1 Int))
            Bool
            (and (= sample-id-0
                    sample-id-1)
                 (= offset-0
                    0)
                 (= offset-1
                    0)))
(define-fun package-invariant!small_composition-rand!
            ((game <GameState_SmallComposition_<$<!n!>$>>))
            Bool
            (let ((pkg (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> game)))
                 (let ((pkg.ctr (<pkg-state-Rand-<$<!n!>$>-ctr> pkg)))
                      (>= pkg.ctr
                          0))))
(define-fun package-invariant!medium_composition-rand!
            ((game <GameState_MediumComposition_<$<!n!>$>>))
            Bool
            (let ((pkg (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> game)))
                 (let ((pkg.ctr (<pkg-state-Rand-<$<!n!>$>-ctr> pkg)))
                      (>= pkg.ctr
                          0))))
(define-fun game-invariant!medium_composition!
            ((game <GameState_MediumComposition_<$<!n!>$>>))
            Bool
            (let ((game.rand (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> game))
                  (game.fwd (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> game)))
                 (let ((game.rand.ctr (<pkg-state-Rand-<$<!n!>$>-ctr> game.rand))
                       (game.fwd.ctr (<pkg-state-Fwd-<$<!n!>$>-ctr> game.fwd)))
                      (and (< (- 1)
                              game.rand.ctr)))))
(define-fun invariant
            ((state-0 <GameState_SmallComposition_<$<!n!>$>>)
             (state-1 <GameState_MediumComposition_<$<!n!>$>>))
            Bool
            (let ((state-0.rand (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> state-0))
                  (state-1.rand (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> state-1))
                  (state-1.fwd (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> state-1)))
                 (let ((state-0.rand.ctr (<pkg-state-Rand-<$<!n!>$>-ctr> state-0.rand))
                       (state-1.rand.ctr (<pkg-state-Rand-<$<!n!>$>-ctr> state-1.rand))
                       (state-1.fwd.ctr (<pkg-state-Fwd-<$<!n!>$>-ctr> state-1.fwd)))
                      (let ((ctr-0 (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> state-0)))
                            (ctr-1 (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> state-1))))
                           (= ctr-0
                              ctr-1)))))
(assert (not (=> (and (forall ((randmap-sample-id-left SampleId)
                               (randmap-sample-offset-left Int)
                               (randmap-sample-id-right SampleId)
                               (randmap-sample-offset-right Int))
                              (=> (randomness-mapping-UsefulOracle randmap-sample-id-left
                                                                   randmap-sample-id-right
                                                                   randmap-sample-offset-left
                                                                   randmap-sample-offset-right)
                                  (rand-is-eq randmap-sample-id-left
                                              randmap-sample-id-right
                                              randmap-sample-offset-left
                                              randmap-sample-offset-right)))
                      (invariant <<game-state-small_composition-old>>
                                 <<game-state-medium_composition-old>>)
                      (package-invariant!small_composition-rand! <<game-state-small_composition-old>>)
                      (package-invariant!medium_composition-rand! <<game-state-medium_composition-old>>)
                      (game-invariant!medium_composition! <<game-state-medium_composition-old>>)
                      (<relation-no-abort-small_composition-medium_composition-UsefulOracle> <<game-state-small_composition-old>>
                                                                                             <<game-state-medium_composition-old>>
                                                                                             <return-small_composition-UsefulOracle>
                                                                                             <return-medium_composition-UsefulOracle>))
                 (package-invariant!small_composition-rand! <<game-state-small_composition-new-UsefulOracle>>))))

(check-sat)
