(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (- (/ 6625690156816701 4503599627370496)) r3))) (let ((.def_1 (* (- (/ 794120259578339 9007199254740992)) r2))) (let ((.def_2 (* (/ 1297527393040575 2251799813685248) r1))) (let ((.def_3 (* (/ 193473478452917 140737488355328) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 273082465605285 2251799813685248))))) (let ((.def_6 (not b3))) (let ((.def_7 (not b1))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (/ 1384180944835765 2251799813685248) r3))) (let ((.def_10 (* (- (/ 799622986398879 2251799813685248)) r2))) (let ((.def_11 (* (- (/ 1151575086131691 2251799813685248)) r1))) (let ((.def_12 (* (/ 2229353711801373 4503599627370496) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (- (/ 717849736961975 2251799813685248))))) (let ((.def_15 (or .def_6 b1 .def_14))) (let ((.def_16 (* (/ 866943917291001 4503599627370496) r3))) (let ((.def_17 (* (- (/ 2147456349051419 9007199254740992)) r2))) (let ((.def_18 (* (- (/ 151829072027083 140737488355328)) r1))) (let ((.def_19 (* (- (/ 3772552513780079 4503599627370496)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 5246993909041133 4503599627370496))))) (let ((.def_22 (not b0))) (let ((.def_23 (or .def_6 .def_22 .def_21))) (let ((.def_24 (* (/ 351956482317181 1125899906842624) r3))) (let ((.def_25 (* (- (/ 7046125568775819 4503599627370496)) r2))) (let ((.def_26 (* (- (/ 1257769208588553 2251799813685248)) r1))) (let ((.def_27 (* (/ 1262644507075181 4503599627370496) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (- (/ 3203788540059449 4503599627370496))))) (let ((.def_30 (not b2))) (let ((.def_31 (or b1 .def_30 .def_29))) (let ((.def_32 (and .def_31 .def_23 .def_15 .def_8))) .def_32))))))))))))))))))))))))))))))))))
(check-sat)
