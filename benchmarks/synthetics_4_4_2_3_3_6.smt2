(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (/ 4580579750738505 4503599627370496) r3))) (let ((.def_1 (* (/ 1697069455500365 1125899906842624) r2))) (let ((.def_2 (* (- (/ 2172510137014781 2251799813685248)) r1))) (let ((.def_3 (* (/ 1095938167283069 1125899906842624) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1137367908277751 1125899906842624)))) (let ((.def_6 (* (/ 427684049606197 140737488355328) r3))) (let ((.def_7 (* (- (/ 2022296787740449 4503599627370496)) r2))) (let ((.def_8 (* (/ 1646835187304241 2251799813685248) r1))) (let ((.def_9 (* (- (/ 429500046395175 9007199254740992)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 4958592926519421 4503599627370496)))) (let ((.def_12 (* (/ 3394739343648145 1125899906842624) r3))) (let ((.def_13 (* (/ 5215411462954143 9007199254740992) r2))) (let ((.def_14 (* (/ 6142307260419829 2251799813685248) r1))) (let ((.def_15 (* (- (/ 1869184321473765 1125899906842624)) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (/ 2357834854606653 2251799813685248)))) (let ((.def_18 (or .def_17 .def_11 .def_5))) (let ((.def_19 (* (/ 2003023746423083 1125899906842624) r3))) (let ((.def_20 (* (- (/ 2747094895166525 4503599627370496)) r2))) (let ((.def_21 (* (- (/ 4193543112700883 4503599627370496)) r1))) (let ((.def_22 (* (/ 1919897936795791 2251799813685248) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (/ 3229380353682787 4503599627370496)))) (let ((.def_25 (* (/ 5175322875814937 9007199254740992) r3))) (let ((.def_26 (* (- (/ 8743852961692821 4503599627370496)) r2))) (let ((.def_27 (* (/ 8676549736891849 4503599627370496) r1))) (let ((.def_28 (* (/ 1163523161583475 4503599627370496) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (- (/ 41871434773463 1125899906842624))))) (let ((.def_31 (* (/ 1735014018710777 1125899906842624) r3))) (let ((.def_32 (* (/ 859317989562885 562949953421312) r2))) (let ((.def_33 (* (/ 2993302198111605 4503599627370496) r1))) (let ((.def_34 (* (/ 7610811892101489 4503599627370496) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 4798487244416947 2251799813685248)))) (let ((.def_37 (or .def_36 .def_30 .def_24))) (let ((.def_38 (and .def_37 .def_18))) .def_38))))))))))))))))))))))))))))))))))))))))
(check-sat)
