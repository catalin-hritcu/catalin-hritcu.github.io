open Prims
let swap_add_sub:
  Prims.int FStar_ST.ref -> Prims.int FStar_ST.ref -> Prims.unit =
  fun r1  ->
    fun r2  ->
      (let uu____70 =
         let uu____71 = FStar_ST.op_Bang r1 in
         let uu____132 = FStar_ST.op_Bang r2 in uu____71 + uu____132 in
       FStar_ST.op_Colon_Equals r1 uu____70);
      (let uu____254 =
         let uu____255 = FStar_ST.op_Bang r1 in
         let uu____316 = FStar_ST.op_Bang r2 in uu____255 - uu____316 in
       FStar_ST.op_Colon_Equals r2 uu____254);
      (let uu____437 =
         let uu____438 = FStar_ST.op_Bang r1 in
         let uu____499 = FStar_ST.op_Bang r2 in uu____438 - uu____499 in
       FStar_ST.op_Colon_Equals r1 uu____437)
let main: Prims.unit =
  let r1 = FStar_ST.alloc (Prims.parse_int "1") in
  let r2 = FStar_ST.alloc (Prims.parse_int "2") in
  swap_add_sub r1 r2;
  (let uu____1155 =
     let uu____1156 =
       let uu____1157 =
         let uu____1158 = FStar_ST.op_Bang r1 in
         Prims.string_of_int uu____1158 in
       let uu____1301 =
         let uu____1302 =
           let uu____1303 =
             let uu____1304 =
               let uu____1305 = FStar_ST.op_Bang r2 in
               Prims.string_of_int uu____1305 in
             Prims.strcat uu____1304 "\n" in
           Prims.strcat "r2=" uu____1303 in
         Prims.strcat "; " uu____1302 in
       Prims.strcat uu____1157 uu____1301 in
     Prims.strcat "r1=" uu____1156 in
   FStar_IO.print_string uu____1155)