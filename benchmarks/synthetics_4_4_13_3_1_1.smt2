(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (- (/ 1752314935358137 9007199254740992)) r3))) (let ((.def_1 (* (/ 6085724139417901 9007199254740992) r2))) (let ((.def_2 (* (/ 899858864037025 2251799813685248) r1))) (let ((.def_3 (* (- (/ 6378390144694937 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1646833137283 9007199254740992))))) (let ((.def_6 (not b1))) (let ((.def_7 (not b3))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (- (/ 3672315389469897 2251799813685248)) r3))) (let ((.def_10 (* (- (/ 2079499407830713 4503599627370496)) r2))) (let ((.def_11 (* (- (/ 5641011133305055 4503599627370496)) r1))) (let ((.def_12 (* (/ 1825928698302259 9007199254740992) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (- (/ 8524615720053411 9007199254740992))))) (let ((.def_15 (not b0))) (let ((.def_16 (or .def_15 .def_6 .def_14))) (let ((.def_17 (* (- (/ 202046672354983 4503599627370496)) r3))) (let ((.def_18 (* (/ 160867041798293 140737488355328) r2))) (let ((.def_19 (* (- (/ 1105738832899407 2251799813685248)) r1))) (let ((.def_20 (* (/ 2492852650502097 4503599627370496) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (/ 2137100991956969 2251799813685248)))) (let ((.def_23 (not b2))) (let ((.def_24 (or .def_23 b1 .def_22))) (let ((.def_25 (* (/ 1219831347558303 4503599627370496) r3))) (let ((.def_26 (* (/ 1865030865585451 4503599627370496) r2))) (let ((.def_27 (* (/ 2437370789356941 2251799813685248) r1))) (let ((.def_28 (* (- (/ 2346685853385157 2251799813685248)) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (/ 1343878520864421 2251799813685248)))) (let ((.def_31 (or .def_7 b2 .def_30))) (let ((.def_32 (* (- (/ 228446600436193 140737488355328)) r3))) (let ((.def_33 (* (/ 5296605730253535 2251799813685248) r2))) (let ((.def_34 (* (- (/ 607243177250433 1125899906842624)) r1))) (let ((.def_35 (* (- (/ 4705543267985799 9007199254740992)) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 5306887373123893 9007199254740992)))) (let ((.def_38 (or .def_6 .def_23 .def_37))) (let ((.def_39 (* (/ 60022312724287 4503599627370496) r3))) (let ((.def_40 (* (- (/ 48064349155413 2251799813685248)) r2))) (let ((.def_41 (* (- (/ 164519421614515 281474976710656)) r1))) (let ((.def_42 (* (- (/ 511739182614109 4503599627370496)) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (- (/ 271112137781505 1125899906842624))))) (let ((.def_45 (or b1 .def_7 .def_44))) (let ((.def_46 (* (/ 111993894951291 4503599627370496) r3))) (let ((.def_47 (* (- (/ 4044739237829373 9007199254740992)) r2))) (let ((.def_48 (* (/ 1777770988251789 1125899906842624) r1))) (let ((.def_49 (* (- (/ 2847886897108195 2251799813685248)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 335556435216371 562949953421312)))) (let ((.def_52 (or .def_15 .def_23 .def_51))) (let ((.def_53 (* (- (/ 2148425437752881 2251799813685248)) r3))) (let ((.def_54 (* (/ 614375093908169 9007199254740992) r2))) (let ((.def_55 (* (/ 4373483003649129 9007199254740992) r1))) (let ((.def_56 (* (- (/ 738084036138691 9007199254740992)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 189158065683465 9007199254740992)))) (let ((.def_59 (or b1 b0 .def_58))) (let ((.def_60 (* (- (/ 7943131241842299 4503599627370496)) r3))) (let ((.def_61 (* (- (/ 2176284596178097 9007199254740992)) r2))) (let ((.def_62 (* (- (/ 1484886208742239 2251799813685248)) r1))) (let ((.def_63 (* (/ 489465451241897 9007199254740992) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 1833721822061291 2251799813685248))))) (let ((.def_66 (or b0 .def_7 .def_65))) (let ((.def_67 (* (/ 814741264633303 2251799813685248) r3))) (let ((.def_68 (* (/ 1122116911920513 1125899906842624) r2))) (let ((.def_69 (* (- (/ 2675953105482111 4503599627370496)) r1))) (let ((.def_70 (* (- (/ 2708596409472147 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 159913283543437 1125899906842624)))) (let ((.def_73 (or .def_7 b2 .def_72))) (let ((.def_74 (* (- (/ 1965423331420115 4503599627370496)) r3))) (let ((.def_75 (* (- (/ 1682709853065197 4503599627370496)) r2))) (let ((.def_76 (* (/ 8435519427679021 9007199254740992) r1))) (let ((.def_77 (* (/ 1894333449773155 4503599627370496) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 2832177187754221 4503599627370496)))) (let ((.def_80 (or .def_7 b0 .def_79))) (let ((.def_81 (* (- (/ 223776053952655 9007199254740992)) r3))) (let ((.def_82 (* (/ 484871312258041 562949953421312) r2))) (let ((.def_83 (* (- (/ 3223483304005135 2251799813685248)) r1))) (let ((.def_84 (* (- (/ 3826023343196365 4503599627370496)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 1782522696020393 4503599627370496))))) (let ((.def_87 (or b1 b2 .def_86))) (let ((.def_88 (* (/ 2559232466846611 9007199254740992) r3))) (let ((.def_89 (* (/ 1470573349023929 4503599627370496) r2))) (let ((.def_90 (* (- (/ 1740370831390585 4503599627370496)) r1))) (let ((.def_91 (* (- (/ 1274846285510189 1125899906842624)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 215431422811777 9007199254740992))))) (let ((.def_94 (or b2 b1 .def_93))) (let ((.def_95 (and .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_38 .def_31 .def_24 .def_16 .def_8))) .def_95)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)