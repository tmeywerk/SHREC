(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b2 () Bool)
(assert (let ((.def_0 (* (- (/ 4241871064198923 9007199254740992)) r3))) (let ((.def_1 (* (/ 4134779621028697 9007199254740992) r2))) (let ((.def_2 (* (/ 3594394023085547 4503599627370496) r1))) (let ((.def_3 (* (- (/ 1029087993191013 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 84244190675739 562949953421312)))) (let ((.def_6 (not b1))) (let ((.def_7 (or b2 .def_6 .def_5))) (let ((.def_8 (* (/ 1429449456574035 4503599627370496) r3))) (let ((.def_9 (* (/ 5421362601721631 9007199254740992) r2))) (let ((.def_10 (* (- (/ 6661854659412935 9007199254740992)) r1))) (let ((.def_11 (* (- (/ 6550552741221351 9007199254740992)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 156116747064365 281474976710656))))) (let ((.def_14 (or b1 b3 .def_13))) (let ((.def_15 (* (- (/ 8766107687338309 9007199254740992)) r3))) (let ((.def_16 (* (- (/ 1797668484658477 9007199254740992)) r2))) (let ((.def_17 (* (/ 435609152056987 9007199254740992) r1))) (let ((.def_18 (* (/ 4094855133155147 2251799813685248) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 4358567722071707 9007199254740992)))) (let ((.def_21 (not b2))) (let ((.def_22 (or .def_21 b0 .def_20))) (let ((.def_23 (* (- (/ 4023746596780547 9007199254740992)) r3))) (let ((.def_24 (* (- (/ 464929914669149 9007199254740992)) r2))) (let ((.def_25 (* (- (/ 3649834256835985 2251799813685248)) r1))) (let ((.def_26 (* (- (/ 3219280152795683 2251799813685248)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (- (/ 1133407334388215 562949953421312))))) (let ((.def_29 (or b0 b2 .def_28))) (let ((.def_30 (* (- (/ 1589987410317639 4503599627370496)) r3))) (let ((.def_31 (* (/ 4738937215395805 9007199254740992) r2))) (let ((.def_32 (* (- (/ 4178120021433697 9007199254740992)) r1))) (let ((.def_33 (* (- (/ 3417148490625409 4503599627370496)) r0))) (let ((.def_34 (+ .def_33 .def_32 .def_31 .def_30))) (let ((.def_35 (<= .def_34 (- (/ 1915089442231865 4503599627370496))))) (let ((.def_36 (or b2 b3 .def_35))) (let ((.def_37 (and .def_36 .def_29 .def_22 .def_14 .def_7))) .def_37)))))))))))))))))))))))))))))))))))))))
(check-sat)