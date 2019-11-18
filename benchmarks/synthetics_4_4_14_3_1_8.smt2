(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 2580007765901249 4503599627370496) r3))) (let ((.def_1 (* (/ 2182972726996873 2251799813685248) r2))) (let ((.def_2 (* (/ 3113081372202003 9007199254740992) r1))) (let ((.def_3 (* (- (/ 3697529676814363 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1873220828248241 2251799813685248)))) (let ((.def_6 (not b0))) (let ((.def_7 (or .def_6 b2 .def_5))) (let ((.def_8 (* (/ 509522297075443 562949953421312) r3))) (let ((.def_9 (* (- (/ 1427642638023823 9007199254740992)) r2))) (let ((.def_10 (* (- (/ 161906711776265 1125899906842624)) r1))) (let ((.def_11 (* (- (/ 1708967996323711 1125899906842624)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 2837873400255323 9007199254740992))))) (let ((.def_14 (not b3))) (let ((.def_15 (or .def_14 b1 .def_13))) (let ((.def_16 (* (/ 1191347559004955 2251799813685248) r3))) (let ((.def_17 (* (/ 774294774179255 1125899906842624) r2))) (let ((.def_18 (* (- (/ 4438066801389641 9007199254740992)) r1))) (let ((.def_19 (* (- (/ 6932734492854759 9007199254740992)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (/ 332888528988133 2251799813685248)))) (let ((.def_22 (or b1 .def_6 .def_21))) (let ((.def_23 (* (- (/ 286335177035439 281474976710656)) r3))) (let ((.def_24 (* (- (/ 2326085253909437 1125899906842624)) r2))) (let ((.def_25 (* (- (/ 379945731015801 1125899906842624)) r1))) (let ((.def_26 (* (/ 724075132030057 9007199254740992) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (- (/ 4280844457351657 4503599627370496))))) (let ((.def_29 (or .def_6 .def_14 .def_28))) (let ((.def_30 (* (/ 3282201572152503 2251799813685248) r3))) (let ((.def_31 (* (- (/ 284301424865671 281474976710656)) r2))) (let ((.def_32 (* (- (/ 6502624889950363 9007199254740992)) r1))) (let ((.def_33 (* (- (/ 2328954243470003 4503599627370496)) r0))) (let ((.def_34 (+ .def_33 .def_32 .def_31 .def_30))) (let ((.def_35 (<= .def_34 (/ 1445245701312799 9007199254740992)))) (let ((.def_36 (or b3 b0 .def_35))) (let ((.def_37 (* (/ 1251243072412391 4503599627370496) r3))) (let ((.def_38 (* (/ 1776176331803079 2251799813685248) r2))) (let ((.def_39 (* (- (/ 1024849322010199 562949953421312)) r1))) (let ((.def_40 (* (- (/ 6239370309924663 9007199254740992)) r0))) (let ((.def_41 (+ .def_40 .def_39 .def_38 .def_37))) (let ((.def_42 (<= .def_41 (- (/ 7083752522951419 9007199254740992))))) (let ((.def_43 (not b2))) (let ((.def_44 (or .def_6 .def_43 .def_42))) (let ((.def_45 (* (/ 265056670525967 562949953421312) r3))) (let ((.def_46 (* (- (/ 3762079695894195 4503599627370496)) r2))) (let ((.def_47 (* (/ 4810081761881571 4503599627370496) r1))) (let ((.def_48 (* (/ 4462910600976411 9007199254740992) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 4298835873163389 4503599627370496)))) (let ((.def_51 (not b1))) (let ((.def_52 (or b0 .def_51 .def_50))) (let ((.def_53 (* (/ 498846255380259 2251799813685248) r3))) (let ((.def_54 (* (/ 764900655532691 562949953421312) r2))) (let ((.def_55 (* (- (/ 1706176351383617 2251799813685248)) r1))) (let ((.def_56 (* (- (/ 8368623822913047 9007199254740992)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 654322272578373 2251799813685248)))) (let ((.def_59 (or .def_43 .def_6 .def_58))) (let ((.def_60 (* (/ 344359832065823 562949953421312) r3))) (let ((.def_61 (* (/ 593757712504615 562949953421312) r2))) (let ((.def_62 (* (- (/ 1888310845159061 2251799813685248)) r1))) (let ((.def_63 (* (/ 663325551291241 4503599627370496) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 4313537225710865 4503599627370496)))) (let ((.def_66 (or b1 b3 .def_65))) (let ((.def_67 (* (/ 1768639407833845 9007199254740992) r3))) (let ((.def_68 (* (- (/ 617235099278997 4503599627370496)) r2))) (let ((.def_69 (* (- (/ 2061776039367795 1125899906842624)) r1))) (let ((.def_70 (* (/ 450973004967661 4503599627370496) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 72918355824687 281474976710656))))) (let ((.def_73 (or .def_43 .def_6 .def_72))) (let ((.def_74 (* (- (/ 3280806807581769 4503599627370496)) r3))) (let ((.def_75 (* (/ 3428837566879997 4503599627370496) r2))) (let ((.def_76 (* (/ 7264597772837755 9007199254740992) r1))) (let ((.def_77 (* (- (/ 89657278056479 140737488355328)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 4393441079311895 9007199254740992)))) (let ((.def_80 (or b0 b1 .def_79))) (let ((.def_81 (* (/ 286742825236305 4503599627370496) r3))) (let ((.def_82 (* (/ 1094932768056227 1125899906842624) r2))) (let ((.def_83 (* (- (/ 3419813152018487 4503599627370496)) r1))) (let ((.def_84 (* (- (/ 235120842506815 9007199254740992)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 1058811837609777 2251799813685248)))) (let ((.def_87 (or .def_51 .def_6 .def_86))) (let ((.def_88 (* (- (/ 2474069502295335 1125899906842624)) r3))) (let ((.def_89 (* (- (/ 2675807004789661 2251799813685248)) r2))) (let ((.def_90 (* (/ 1270437595858877 4503599627370496) r1))) (let ((.def_91 (* (- (/ 545541454438145 4503599627370496)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 516890731462837 562949953421312))))) (let ((.def_94 (or b0 b3 .def_93))) (let ((.def_95 (* (- (/ 2585795525331005 2251799813685248)) r3))) (let ((.def_96 (* (- (/ 710292598762389 9007199254740992)) r2))) (let ((.def_97 (* (- (/ 5936844124882611 2251799813685248)) r1))) (let ((.def_98 (* (/ 1067825368509593 9007199254740992) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (- (/ 522193339508285 562949953421312))))) (let ((.def_101 (or b1 b0 .def_100))) (let ((.def_102 (and .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_44 .def_36 .def_29 .def_22 .def_15 .def_7))) .def_102))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)