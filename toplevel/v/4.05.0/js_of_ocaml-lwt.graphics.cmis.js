// Generated by js_of_ocaml 3.0.1+git-796279c1
(function(a)
   {"use strict";
    function b(c,b)
     {if(a.caml_create_file)
       a.caml_create_file(c,b);
      else
       {if(!a.caml_fs_tmp)a.caml_fs_tmp = [];
        a.caml_fs_tmp.push({name:c,content:b})}
      return 0}
    b
     ("/static/cmis/graphics_js.cmi",
      "Caml1999I021\x84\x95\xa6\xbe\0\0\x1d\xf5\0\0\x06\n\0\0\x16D\0\0\x15\x9a\xa0+Graphics_js\xa0\xb2\xb0\x01\b\xa7/Graphic_failure@\xf0\x90\xb0G#exn@@\x90\xa0\xb0\xb3\x90\xb0O&string@@\x90@\x02\x05\xf5\xe1\0\0\xfe@@A\xb0\xc0&_none_A@\0\xff\x04\x02A@B\xa0\xa0\xb0\x01\b\xa8+close_graph@\xc0\xb0\xc1@\xb0\xb3\x90\xb0F$unit@@\x90@\x02\x05\xf5\xe1\0\0\xfb\xb0\xb3\x04\x06@\x90@\x02\x05\xf5\xe1\0\0\xfc@\x02\x05\xf5\xe1\0\0\xfd@\x04\x13@\xa0\xa0\xb0\x01\b\xa90set_window_title@\xc0\xb0\xc1@\xb0\xb3\x04 @\x90@\x02\x05\xf5\xe1\0\0\xf8\xb0\xb3\x04\x13@\x90@\x02\x05\xf5\xe1\0\0\xf9@\x02\x05\xf5\xe1\0\0\xfa@\x04 @\xa0\xa0\xb0\x01\b\xaa-resize_window@\xc0\xb0\xc1@\xb0\xb3\x90\xb0A#int@@\x90@\x02\x05\xf5\xe1\0\0\xf3\xb0\xc1@\xb0\xb3\x04\b@\x90@\x02\x05\xf5\xe1\0\0\xf4\xb0\xb3\x04(@\x90@\x02\x05\xf5\xe1\0\0\xf5@\x02\x05\xf5\xe1\0\0\xf6@\x02\x05\xf5\xe1\0\0\xf7@\x045@\xa0\xa0\xb0\x01\b\xab+clear_graph@\xc0\xb0\xc1@\xb0\xb3\x042@\x90@\x02\x05\xf5\xe1\0\0\xf0\xb0\xb3\x045@\x90@\x02\x05\xf5\xe1\0\0\xf1@\x02\x05\xf5\xe1\0\0\xf2\x90\xe03caml_gr_clear_graphAA \xa0@@@\x04G@\xa0\xa0\xb0\x01\b\xac&size_x@\xc0\xb0\xc1@\xb0\xb3\x04D@\x90@\x02\x05\xf5\xe1\0\0\xed\xb0\xb3\x04*@\x90@\x02\x05\xf5\xe1\0\0\xee@\x02\x05\xf5\xe1\0\0\xef\x90\xe0.caml_gr_size_xAA\x04\x12\xa0@@@\x04X@\xa0\xa0\xb0\x01\b\xad&size_y@\xc0\xb0\xc1@\xb0\xb3\x04U@\x90@\x02\x05\xf5\xe1\0\0\xea\xb0\xb3\x04;@\x90@\x02\x05\xf5\xe1\0\0\xeb@\x02\x05\xf5\xe1\0\0\xec\x90\xe0.caml_gr_size_yAA\x04#\xa0@@@\x04i@\xa0\xb1\xb0\x01\b\xae%color@\b\0\0,\0@@@A\x90\xb0\xb3\x04H@\x90@\x02\x05\xf5\xe1\0\0\xe9@@\x04r@A\xa0@@A\xa0\xa0\xb0\x01\b\xaf#rgb@\xc0\xb0\xc1@\xb0\xb3\x04S@\x90@\x02\x05\xf5\xe1\0\0\xe2\xb0\xc1@\xb0\xb3\x04X@\x90@\x02\x05\xf5\xe1\0\0\xe3\xb0\xc1@\xb0\xb3\x04]@\x90@\x02\x05\xf5\xe1\0\0\xe4\xb0\xb3\x90\x04\x1f@\x90@\x02\x05\xf5\xe1\0\0\xe5@\x02\x05\xf5\xe1\0\0\xe6@\x02\x05\xf5\xe1\0\0\xe7@\x02\x05\xf5\xe1\0\0\xe8@\x04\x8b@\xa0\xa0\xb0\x01\b\xb0)set_color@\xc0\xb0\xc1@\xb0\xb3\x04\x0b@\x90@\x02\x05\xf5\xe1\0\0\xdf\xb0\xb3\x04\x8b@\x90@\x02\x05\xf5\xe1\0\0\xe0@\x02\x05\xf5\xe1\0\0\xe1\x90\xe01caml_gr_set_colorAA\x04V\xa0@@@\x04\x9c@\xa0\xa0\xb0\x01\b\xb1*background@\xc0\xb0\xb3\x04\x1a@\x90@\x02\x05\xf5\xe1\0\0\xde@\x04\xa4@\xa0\xa0\xb0\x01\b\xb2*foreground@\xc0\xb0\xb3\x04\"@\x90@\x02\x05\xf5\xe1\0\0\xdd@\x04\xac@\xa0\xa0\xb0\x01\b\xb3%black@\xc0\xb0\xb3\x04*@\x90@\x02\x05\xf5\xe1\0\0\xdc@\x04\xb4@\xa0\xa0\xb0\x01\b\xb4%white@\xc0\xb0\xb3\x042@\x90@\x02\x05\xf5\xe1\0\0\xdb@\x04\xbc@\xa0\xa0\xb0\x01\b\xb5#red@\xc0\xb0\xb3\x04:@\x90@\x02\x05\xf5\xe1\0\0\xda@\x04\xc4@\xa0\xa0\xb0\x01\b\xb6%green@\xc0\xb0\xb3\x04B@\x90@\x02\x05\xf5\xe1\0\0\xd9@\x04\xcc@\xa0\xa0\xb0\x01\b\xb7$blue@\xc0\xb0\xb3\x04J@\x90@\x02\x05\xf5\xe1\0\0\xd8@\x04\xd4@\xa0\xa0\xb0\x01\b\xb8&yellow@\xc0\xb0\xb3\x04R@\x90@\x02\x05\xf5\xe1\0\0\xd7@\x04\xdc@\xa0\xa0\xb0\x01\b\xb9$cyan@\xc0\xb0\xb3\x04Z@\x90@\x02\x05\xf5\xe1\0\0\xd6@\x04\xe4@\xa0\xa0\xb0\x01\b\xba'magenta@\xc0\xb0\xb3\x04b@\x90@\x02\x05\xf5\xe1\0\0\xd5@\x04\xec@\xa0\xa0\xb0\x01\b\xbb$plot@\xc0\xb0\xc1@\xb0\xb3\x04\xcc@\x90@\x02\x05\xf5\xe1\0\0\xd0\xb0\xc1@\xb0\xb3\x04\xd1@\x90@\x02\x05\xf5\xe1\0\0\xd1\xb0\xb3\x04\xf1@\x90@\x02\x05\xf5\xe1\0\0\xd2@\x02\x05\xf5\xe1\0\0\xd3@\x02\x05\xf5\xe1\0\0\xd4\x90\xe0,caml_gr_plotBA\x04\xbc\xa0@\xa0@@@\x05\x01\x03@\xa0\xa0\xb0\x01\b\xbc%plots@\xc0\xb0\xc1@\xb0\xb3\x90\xb0H%array@\xa0\xb0\x92\xa0\xb0\xb3\x04\xec@\x90@\x02\x05\xf5\xe1\0\0\xcb\xa0\xb0\xb3\x04\xf0@\x90@\x02\x05\xf5\xe1\0\0\xca@\x02\x05\xf5\xe1\0\0\xcc@\x90@\x02\x05\xf5\xe1\0\0\xcd\xb0\xb3\x05\x01\x11@\x90@\x02\x05\xf5\xe1\0\0\xce@\x02\x05\xf5\xe1\0\0\xcf@\x05\x01\x1e@\xa0\xa0\xb0\x01\b\xbd+point_color@\xc0\xb0\xc1@\xb0\xb3\x04\xfe@\x90@\x02\x05\xf5\xe1\0\0\xc5\xb0\xc1@\xb0\xb3\x05\x01\x03@\x90@\x02\x05\xf5\xe1\0\0\xc6\xb0\xb3\x04\xa6@\x90@\x02\x05\xf5\xe1\0\0\xc7@\x02\x05\xf5\xe1\0\0\xc8@\x02\x05\xf5\xe1\0\0\xc9\x90\xe03caml_gr_point_colorBA\x04\xee\xa0@\xa0@@@\x05\x015@\xa0\xa0\xb0\x01\b\xbe&moveto@\xc0\xb0\xc1@\xb0\xb3\x05\x01\x15@\x90@\x02\x05\xf5\xe1\0\0\xc0\xb0\xc1@\xb0\xb3\x05\x01\x1a@\x90@\x02\x05\xf5\xe1\0\0\xc1\xb0\xb3\x05\x01:@\x90@\x02\x05\xf5\xe1\0\0\xc2@\x02\x05\xf5\xe1\0\0\xc3@\x02\x05\xf5\xe1\0\0\xc4\x90\xe0.caml_gr_movetoBA\x05\x01\x05\xa0@\xa0@@@\x05\x01L@\xa0\xa0\xb0\x01\b\xbf'rmoveto@\xc0\xb0\xc1@\xb0\xb3\x05\x01,@\x90@\x02\x05\xf5\xe1\0\0\xbb\xb0\xc1@\xb0\xb3\x05\x011@\x90@\x02\x05\xf5\xe1\0\0\xbc\xb0\xb3\x05\x01Q@\x90@\x02\x05\xf5\xe1\0\0\xbd@\x02\x05\xf5\xe1\0\0\xbe@\x02\x05\xf5\xe1\0\0\xbf@\x05\x01^@\xa0\xa0\xb0\x01\b\xc0)current_x@\xc0\xb0\xc1@\xb0\xb3\x05\x01[@\x90@\x02\x05\xf5\xe1\0\0\xb8\xb0\xb3\x05\x01A@\x90@\x02\x05\xf5\xe1\0\0\xb9@\x02\x05\xf5\xe1\0\0\xba\x90\xe01caml_gr_current_xAA\x05\x01)\xa0@@@\x05\x01o@\xa0\xa0\xb0\x01\b\xc1)current_y@\xc0\xb0\xc1@\xb0\xb3\x05\x01l@\x90@\x02\x05\xf5\xe1\0\0\xb5\xb0\xb3\x05\x01R@\x90@\x02\x05\xf5\xe1\0\0\xb6@\x02\x05\xf5\xe1\0\0\xb7\x90\xe01caml_gr_current_yAA\x05\x01:\xa0@@@\x05\x01\x80@\xa0\xa0\xb0\x01\b\xc2-current_point@\xc0\xb0\xc1@\xb0\xb3\x05\x01}@\x90@\x02\x05\xf5\xe1\0\0\xb0\xb0\x92\xa0\xb0\xb3\x05\x01f@\x90@\x02\x05\xf5\xe1\0\0\xb2\xa0\xb0\xb3\x05\x01j@\x90@\x02\x05\xf5\xe1\0\0\xb1@\x02\x05\xf5\xe1\0\0\xb3@\x02\x05\xf5\xe1\0\0\xb4@\x05\x01\x94@\xa0\xa0\xb0\x01\b\xc3&lineto@\xc0\xb0\xc1@\xb0\xb3\x05\x01t@\x90@\x02\x05\xf5\xe1\0\0\xab\xb0\xc1@\xb0\xb3\x05\x01y@\x90@\x02\x05\xf5\xe1\0\0\xac\xb0\xb3\x05\x01\x99@\x90@\x02\x05\xf5\xe1\0\0\xad@\x02\x05\xf5\xe1\0\0\xae@\x02\x05\xf5\xe1\0\0\xaf\x90\xe0.caml_gr_linetoBA\x05\x01d\xa0@\xa0@@@\x05\x01\xab@\xa0\xa0\xb0\x01\b\xc4'rlineto@\xc0\xb0\xc1@\xb0\xb3\x05\x01\x8b@\x90@\x02\x05\xf5\xe1\0\0\xa6\xb0\xc1@\xb0\xb3\x05\x01\x90@\x90@\x02\x05\xf5\xe1\0\0\xa7\xb0\xb3\x05\x01\xb0@\x90@\x02\x05\xf5\xe1\0\0\xa8@\x02\x05\xf5\xe1\0\0\xa9@\x02\x05\xf5\xe1\0\0\xaa@\x05\x01\xbd@\xa0\xa0\xb0\x01\b\xc5'curveto@\xc0\xb0\xc1@\xb0\x92\xa0\xb0\xb3\x05\x01\xa0@\x90@\x02\x05\xf5\xe1\0\0\x9a\xa0\xb0\xb3\x05\x01\xa4@\x90@\x02\x05\xf5\xe1\0\0\x99@\x02\x05\xf5\xe1\0\0\x9b\xb0\xc1@\xb0\x92\xa0\xb0\xb3\x05\x01\xac@\x90@\x02\x05\xf5\xe1\0\0\x9d\xa0\xb0\xb3\x05\x01\xb0@\x90@\x02\x05\xf5\xe1\0\0\x9c@\x02\x05\xf5\xe1\0\0\x9e\xb0\xc1@\xb0\x92\xa0\xb0\xb3\x05\x01\xb8@\x90@\x02\x05\xf5\xe1\0\0\xa0\xa0\xb0\xb3\x05\x01\xbc@\x90@\x02\x05\xf5\xe1\0\0\x9f@\x02\x05\xf5\xe1\0\0\xa1\xb0\xb3\x05\x01\xdc@\x90@\x02\x05\xf5\xe1\0\0\xa2@\x02\x05\xf5\xe1\0\0\xa3@\x02\x05\xf5\xe1\0\0\xa4@\x02\x05\xf5\xe1\0\0\xa5@\x05\x01\xe9@\xa0\xa0\xb0\x01\b\xc6)draw_rect@\xc0\xb0\xc1@\xb0\xb3\x05\x01\xc9@\x90@\x02\x05\xf5\xe1\0\0\x90\xb0\xc1@\xb0\xb3\x05\x01\xce@\x90@\x02\x05\xf5\xe1\0\0\x91\xb0\xc1@\xb0\xb3\x05\x01\xd3@\x90@\x02\x05\xf5\xe1\0\0\x92\xb0\xc1@\xb0\xb3\x05\x01\xd8@\x90@\x02\x05\xf5\xe1\0\0\x93\xb0\xb3\x05\x01\xf8@\x90@\x02\x05\xf5\xe1\0\0\x94@\x02\x05\xf5\xe1\0\0\x95@\x02\x05\xf5\xe1\0\0\x96@\x02\x05\xf5\xe1\0\0\x97@\x02\x05\xf5\xe1\0\0\x98@\x05\x02\x05@\xa0\xa0\xb0\x01\b\xc7.draw_poly_line@\xc0\xb0\xc1@\xb0\xb3\x05\x01\x02\xa0\xb0\x92\xa0\xb0\xb3\x05\x01\xeb@\x90@\x02\x05\xf5\xe1\0\0\x8b\xa0\xb0\xb3\x05\x01\xef@\x90@\x02\x05\xf5\xe1\0\0\x8a@\x02\x05\xf5\xe1\0\0\x8c@\x90@\x02\x05\xf5\xe1\0\0\x8d\xb0\xb3\x05\x02\x10@\x90@\x02\x05\xf5\xe1\0\0\x8e@\x02\x05\xf5\xe1\0\0\x8f@\x05\x02\x1d@\xa0\xa0\xb0\x01\b\xc8)draw_poly@\xc0\xb0\xc1@\xb0\xb3\x05\x01\x1a\xa0\xb0\x92\xa0\xb0\xb3\x05\x02\x03@\x90@\x02\x05\xf5\xe1\0\0\x85\xa0\xb0\xb3\x05\x02\x07@\x90@\x02\x05\xf5\xe1\0\0\x84@\x02\x05\xf5\xe1\0\0\x86@\x90@\x02\x05\xf5\xe1\0\0\x87\xb0\xb3\x05\x02(@\x90@\x02\x05\xf5\xe1\0\0\x88@\x02\x05\xf5\xe1\0\0\x89@\x05\x025@\xa0\xa0\xb0\x01\b\xc9-draw_segments@\xc0\xb0\xc1@\xb0\xb3\x05\x012\xa0\xb0\x92\xa0\xb0\xb3\x05\x02\x1b@\x90@\x02\x05\xf5\xe1\0\x01\xff\x7f\xa0\xb0\xb3\x05\x02\x1f@\x90@\x02\x05\xf5\xe1\0\x01\xff~\xa0\xb0\xb3\x05\x02#@\x90@\x02\x05\xf5\xe1\0\x01\xff}\xa0\xb0\xb3\x05\x02'@\x90@\x02\x05\xf5\xe1\0\x01\xff|@\x02\x05\xf5\xe1\0\0\x80@\x90@\x02\x05\xf5\xe1\0\0\x81\xb0\xb3\x05\x02H@\x90@\x02\x05\xf5\xe1\0\0\x82@\x02\x05\xf5\xe1\0\0\x83@\x05\x02U@\xa0\xa0\xb0\x01\b\xca(draw_arc@\xc0\xb0\xc1@\xb0\xb3\x05\x025@\x90@\x02\x05\xf5\xe1\0\x01\xffo\xb0\xc1@\xb0\xb3\x05\x02:@\x90@\x02\x05\xf5\xe1\0\x01\xffp\xb0\xc1@\xb0\xb3\x05\x02?@\x90@\x02\x05\xf5\xe1\0\x01\xffq\xb0\xc1@\xb0\xb3\x05\x02D@\x90@\x02\x05\xf5\xe1\0\x01\xffr\xb0\xc1@\xb0\xb3\x05\x02I@\x90@\x02\x05\xf5\xe1\0\x01\xffs\xb0\xc1@\xb0\xb3\x05\x02N@\x90@\x02\x05\xf5\xe1\0\x01\xfft\xb0\xb3\x05\x02n@\x90@\x02\x05\xf5\xe1\0\x01\xffu@\x02\x05\xf5\xe1\0\x01\xffv@\x02\x05\xf5\xe1\0\x01\xffw@\x02\x05\xf5\xe1\0\x01\xffx@\x02\x05\xf5\xe1\0\x01\xffy@\x02\x05\xf5\xe1\0\x01\xffz@\x02\x05\xf5\xe1\0\x01\xff{@\x05\x02{@\xa0\xa0\xb0\x01\b\xcb,draw_ellipse@\xc0\xb0\xc1@\xb0\xb3\x05\x02[@\x90@\x02\x05\xf5\xe1\0\x01\xfff\xb0\xc1@\xb0\xb3\x05\x02`@\x90@\x02\x05\xf5\xe1\0\x01\xffg\xb0\xc1@\xb0\xb3\x05\x02e@\x90@\x02\x05\xf5\xe1\0\x01\xffh\xb0\xc1@\xb0\xb3\x05\x02j@\x90@\x02\x05\xf5\xe1\0\x01\xffi\xb0\xb3\x05\x02\x8a@\x90@\x02\x05\xf5\xe1\0\x01\xffj@\x02\x05\xf5\xe1\0\x01\xffk@\x02\x05\xf5\xe1\0\x01\xffl@\x02\x05\xf5\xe1\0\x01\xffm@\x02\x05\xf5\xe1\0\x01\xffn@\x05\x02\x97@\xa0\xa0\xb0\x01\b\xcc+draw_circle@\xc0\xb0\xc1@\xb0\xb3\x05\x02w@\x90@\x02\x05\xf5\xe1\0\x01\xff_\xb0\xc1@\xb0\xb3\x05\x02|@\x90@\x02\x05\xf5\xe1\0\x01\xff`\xb0\xc1@\xb0\xb3\x05\x02\x81@\x90@\x02\x05\xf5\xe1\0\x01\xffa\xb0\xb3\x05\x02\xa1@\x90@\x02\x05\xf5\xe1\0\x01\xffb@\x02\x05\xf5\xe1\0\x01\xffc@\x02\x05\xf5\xe1\0\x01\xffd@\x02\x05\xf5\xe1\0\x01\xffe@\x05\x02\xae@\xa0\xa0\xb0\x01\b\xcd.set_line_width@\xc0\xb0\xc1@\xb0\xb3\x05\x02\x8e@\x90@\x02\x05\xf5\xe1\0\x01\xff\\\xb0\xb3\x05\x02\xae@\x90@\x02\x05\xf5\xe1\0\x01\xff]@\x02\x05\xf5\xe1\0\x01\xff^@\x05\x02\xbb@\xa0\xa0\xb0\x01\b\xce)draw_char@\xc0\xb0\xc1@\xb0\xb3\x90\xb0B$char@@\x90@\x02\x05\xf5\xe1\0\x01\xffY\xb0\xb3\x05\x02\xbe@\x90@\x02\x05\xf5\xe1\0\x01\xffZ@\x02\x05\xf5\xe1\0\x01\xff[\x90\xe01caml_gr_draw_charAA\x05\x02\x89\xa0@@@\x05\x02\xcf@\xa0\xa0\xb0\x01\b\xcf+draw_string@\xc0\xb0\xc1@\xb0\xb3\x05\x02\xdc@\x90@\x02\x05\xf5\xe1\0\x01\xffV\xb0\xb3\x05\x02\xcf@\x90@\x02\x05\xf5\xe1\0\x01\xffW@\x02\x05\xf5\xe1\0\x01\xffX\x90\xe03caml_gr_draw_stringAA\x05\x02\x9a\xa0@@@\x05\x02\xe0@\xa0\xa0\xb0\x01\b\xd0(set_font@\xc0\xb0\xc1@\xb0\xb3\x05\x02\xed@\x90@\x02\x05\xf5\xe1\0\x01\xffS\xb0\xb3\x05\x02\xe0@\x90@\x02\x05\xf5\xe1\0\x01\xffT@\x02\x05\xf5\xe1\0\x01\xffU\x90\xe00caml_gr_set_fontAA\x05\x02\xab\xa0@@@\x05\x02\xf1@\xa0\xa0\xb0\x01\b\xd1-set_text_size@\xc0\xb0\xc1@\xb0\xb3\x05\x02\xd1@\x90@\x02\x05\xf5\xe1\0\x01\xffP\xb0\xb3\x05\x02\xf1@\x90@\x02\x05\xf5\xe1\0\x01\xffQ@\x02\x05\xf5\xe1\0\x01\xffR@\x05\x02\xfe@\xa0\xa0\xb0\x01\b\xd2)text_size@\xc0\xb0\xc1@\xb0\xb3\x05\x03\x0b@\x90@\x02\x05\xf5\xe1\0\x01\xffK\xb0\x92\xa0\xb0\xb3\x05\x02\xe4@\x90@\x02\x05\xf5\xe1\0\x01\xffM\xa0\xb0\xb3\x05\x02\xe8@\x90@\x02\x05\xf5\xe1\0\x01\xffL@\x02\x05\xf5\xe1\0\x01\xffN@\x02\x05\xf5\xe1\0\x01\xffO\x90\xe01caml_gr_text_sizeAA\x05\x02\xd0\xa0@@@\x05\x03\x16@\xa0\xa0\xb0\x01\b\xd3)fill_rect@\xc0\xb0\xc1@\xb0\xb3\x05\x02\xf6@\x90@\x02\x05\xf5\xe1\0\x01\xffB\xb0\xc1@\xb0\xb3\x05\x02\xfb@\x90@\x02\x05\xf5\xe1\0\x01\xffC\xb0\xc1@\xb0\xb3\x05\x03\0@\x90@\x02\x05\xf5\xe1\0\x01\xffD\xb0\xc1@\xb0\xb3\x05\x03\x05@\x90@\x02\x05\xf5\xe1\0\x01\xffE\xb0\xb3\x05\x03%@\x90@\x02\x05\xf5\xe1\0\x01\xffF@\x02\x05\xf5\xe1\0\x01\xffG@\x02\x05\xf5\xe1\0\x01\xffH@\x02\x05\xf5\xe1\0\x01\xffI@\x02\x05\xf5\xe1\0\x01\xffJ@\x05\x032@\xa0\xa0\xb0\x01\b\xd4)fill_poly@\xc0\xb0\xc1@\xb0\xb3\x05\x02/\xa0\xb0\x92\xa0\xb0\xb3\x05\x03\x18@\x90@\x02\x05\xf5\xe1\0\x01\xff=\xa0\xb0\xb3\x05\x03\x1c@\x90@\x02\x05\xf5\xe1\0\x01\xff<@\x02\x05\xf5\xe1\0\x01\xff>@\x90@\x02\x05\xf5\xe1\0\x01\xff?\xb0\xb3\x05\x03=@\x90@\x02\x05\xf5\xe1\0\x01\xff@@\x02\x05\xf5\xe1\0\x01\xffA\x90\xe01caml_gr_fill_polyAA\x05\x03\b\xa0@@@\x05\x03N@\xa0\xa0\xb0\x01\b\xd5(fill_arc@\xc0\xb0\xc1@\xb0\xb3\x05\x03.@\x90@\x02\x05\xf5\xe1\0\x01\xff/\xb0\xc1@\xb0\xb3\x05\x033@\x90@\x02\x05\xf5\xe1\0\x01\xff0\xb0\xc1@\xb0\xb3\x05\x038@\x90@\x02\x05\xf5\xe1\0\x01\xff1\xb0\xc1@\xb0\xb3\x05\x03=@\x90@\x02\x05\xf5\xe1\0\x01\xff2\xb0\xc1@\xb0\xb3\x05\x03B@\x90@\x02\x05\xf5\xe1\0\x01\xff3\xb0\xc1@\xb0\xb3\x05\x03G@\x90@\x02\x05\xf5\xe1\0\x01\xff4\xb0\xb3\x05\x03g@\x90@\x02\x05\xf5\xe1\0\x01\xff5@\x02\x05\xf5\xe1\0\x01\xff6@\x02\x05\xf5\xe1\0\x01\xff7@\x02\x05\xf5\xe1\0\x01\xff8@\x02\x05\xf5\xe1\0\x01\xff9@\x02\x05\xf5\xe1\0\x01\xff:@\x02\x05\xf5\xe1\0\x01\xff;@\x05\x03t@\xa0\xa0\xb0\x01\b\xd6,fill_ellipse@\xc0\xb0\xc1@\xb0\xb3\x05\x03T@\x90@\x02\x05\xf5\xe1\0\x01\xff&\xb0\xc1@\xb0\xb3\x05\x03Y@\x90@\x02\x05\xf5\xe1\0\x01\xff'\xb0\xc1@\xb0\xb3\x05\x03^@\x90@\x02\x05\xf5\xe1\0\x01\xff(\xb0\xc1@\xb0\xb3\x05\x03c@\x90@\x02\x05\xf5\xe1\0\x01\xff)\xb0\xb3\x05\x03\x83@\x90@\x02\x05\xf5\xe1\0\x01\xff*@\x02\x05\xf5\xe1\0\x01\xff+@\x02\x05\xf5\xe1\0\x01\xff,@\x02\x05\xf5\xe1\0\x01\xff-@\x02\x05\xf5\xe1\0\x01\xff.@\x05\x03\x90@\xa0\xa0\xb0\x01\b\xd7+fill_circle@\xc0\xb0\xc1@\xb0\xb3\x05\x03p@\x90@\x02\x05\xf5\xe1\0\x01\xff\x1f\xb0\xc1@\xb0\xb3\x05\x03u@\x90@\x02\x05\xf5\xe1\0\x01\xff \xb0\xc1@\xb0\xb3\x05\x03z@\x90@\x02\x05\xf5\xe1\0\x01\xff!\xb0\xb3\x05\x03\x9a@\x90@\x02\x05\xf5\xe1\0\x01\xff\"@\x02\x05\xf5\xe1\0\x01\xff#@\x02\x05\xf5\xe1\0\x01\xff$@\x02\x05\xf5\xe1\0\x01\xff%@\x05\x03\xa7@\xa0\xb1\xb0\x01\b\xd8%image@\b\0\0,\0@@@A@@@\x05\x03\xac@@\x05\x03:A\xa0\xa0\xb0\x01\b\xd9&transp@\xc0\xb0\xb3\x05\x03*@\x90@\x02\x05\xf5\xe1\0\x01\xff\x1e@\x05\x03\xb4@\xa0\xa0\xb0\x01\b\xda*make_image@\xc0\xb0\xc1@\xb0\xb3\x05\x02\xb1\xa0\xb0\xb3\x05\x02\xb4\xa0\xb0\xb3\x05\x03:@\x90@\x02\x05\xf5\xe1\0\x01\xff\x19@\x90@\x02\x05\xf5\xe1\0\x01\xff\x1a@\x90@\x02\x05\xf5\xe1\0\x01\xff\x1b\xb0\xb3\x90\x04 @\x90@\x02\x05\xf5\xe1\0\x01\xff\x1c@\x02\x05\xf5\xe1\0\x01\xff\x1d\x90\xe02caml_gr_make_imageAA\x05\x03\x88\xa0@@@\x05\x03\xce@\xa0\xa0\xb0\x01\b\xdb*dump_image@\xc0\xb0\xc1@\xb0\xb3\x04\x0f@\x90@\x02\x05\xf5\xe1\0\x01\xff\x14\xb0\xb3\x05\x02\xce\xa0\xb0\xb3\x05\x02\xd1\xa0\xb0\xb3\x05\x03W@\x90@\x02\x05\xf5\xe1\0\x01\xff\x15@\x90@\x02\x05\xf5\xe1\0\x01\xff\x16@\x90@\x02\x05\xf5\xe1\0\x01\xff\x17@\x02\x05\xf5\xe1\0\x01\xff\x18\x90\xe02caml_gr_dump_imageAA\x05\x03\xa1\xa0@@@\x05\x03\xe7@\xa0\xa0\xb0\x01\b\xdc*draw_image@\xc0\xb0\xc1@\xb0\xb3\x04(@\x90@\x02\x05\xf5\xe1\0\x01\xff\r\xb0\xc1@\xb0\xb3\x05\x03\xcc@\x90@\x02\x05\xf5\xe1\0\x01\xff\x0e\xb0\xc1@\xb0\xb3\x05\x03\xd1@\x90@\x02\x05\xf5\xe1\0\x01\xff\x0f\xb0\xb3\x05\x03\xf1@\x90@\x02\x05\xf5\xe1\0\x01\xff\x10@\x02\x05\xf5\xe1\0\x01\xff\x11@\x02\x05\xf5\xe1\0\x01\xff\x12@\x02\x05\xf5\xe1\0\x01\xff\x13\x90\xe02caml_gr_draw_imageCA\x05\x03\xbc\xa0@\xa0@\xa0@@@\x05\x04\x04@\xa0\xa0\xb0\x01\b\xdd)get_image@\xc0\xb0\xc1@\xb0\xb3\x05\x03\xe4@\x90@\x02\x05\xf5\xe1\0\x01\xff\x04\xb0\xc1@\xb0\xb3\x05\x03\xe9@\x90@\x02\x05\xf5\xe1\0\x01\xff\x05\xb0\xc1@\xb0\xb3\x05\x03\xee@\x90@\x02\x05\xf5\xe1\0\x01\xff\x06\xb0\xc1@\xb0\xb3\x05\x03\xf3@\x90@\x02\x05\xf5\xe1\0\x01\xff\x07\xb0\xb3\x04W@\x90@\x02\x05\xf5\xe1\0\x01\xff\b@\x02\x05\xf5\xe1\0\x01\xff\t@\x02\x05\xf5\xe1\0\x01\xff\n@\x02\x05\xf5\xe1\0\x01\xff\x0b@\x02\x05\xf5\xe1\0\x01\xff\f@\x05\x04 @\xa0\xa0\xb0\x01\b\xde,create_image@\xc0\xb0\xc1@\xb0\xb3\x05\x04\0@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xff\xb0\xc1@\xb0\xb3\x05\x04\x05@\x90@\x02\x05\xf5\xe1\0\x01\xff\0\xb0\xb3\x04i@\x90@\x02\x05\xf5\xe1\0\x01\xff\x01@\x02\x05\xf5\xe1\0\x01\xff\x02@\x02\x05\xf5\xe1\0\x01\xff\x03\x90\xe04caml_gr_create_imageBA\x05\x03\xf0\xa0@\xa0@@@\x05\x047@\xa0\xa0\xb0\x01\b\xdf*blit_image@\xc0\xb0\xc1@\xb0\xb3\x04x@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf8\xb0\xc1@\xb0\xb3\x05\x04\x1c@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf9\xb0\xc1@\xb0\xb3\x05\x04!@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xfa\xb0\xb3\x05\x04A@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xfb@\x02\x05\xf5\xe1\0\x01\xfe\xfc@\x02\x05\xf5\xe1\0\x01\xfe\xfd@\x02\x05\xf5\xe1\0\x01\xfe\xfe\x90\xe02caml_gr_blit_imageCA\x05\x04\f\xa0@\xa0@\xa0@@@\x05\x04T@\xa0\xb1\xb0\x01\b\xe0&status@\b\0\0,\0@@\xa0\xa0\xd0\xb0\x01\x04\xef'mouse_x@@\xb0\xb3\x05\x047@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf7\x05\x04a@\xa0\xd0\xb0\x01\x04\xf0'mouse_y@@\xb0\xb3\x05\x04>@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf6\x05\x04h@\xa0\xd0\xb0\x01\x04\xf1&button@@\xb0\xb3\x90\xb0E$bool@@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf5\x05\x04r@\xa0\xd0\xb0\x01\x04\xf2*keypressed@@\xb0\xb3\x04\n@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf4\x05\x04y@\xa0\xd0\xb0\x01\x04\xf3#key@@\xb0\xb3\x05\x01\xbb@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf3\x05\x04\x80@@@A@@@\x05\x04\x80@@\x05\x04\x0eA\xa0\xb1\xb0\x01\b\xe1%event@\b\0\0,\0@@\x91\xa0\xd0\xb0\x01\x04\xf5+Button_down@\x90@@\x05\x04\x8b@\xa0\xd0\xb0\x01\x04\xf6)Button_up@\x90@@\x05\x04\x90@\xa0\xd0\xb0\x01\x04\xf7+Key_pressed@\x90@@\x05\x04\x95@\xa0\xd0\xb0\x01\x04\xf8,Mouse_motion@\x90@@\x05\x04\x9a@\xa0\xd0\xb0\x01\x04\xf9$Poll@\x90@@\x05\x04\x9f@@A@@@\x05\x04\x9f@A\x05\x04-A\xa0\xa0\xb0\x01\b\xe2/wait_next_event@\xc0\xb0\xc1@\xb0\xb3\x90\xb0I$list@\xa0\xb0\xb3\x90\x04-@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xef@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf0\xb0\xb3\x90\x04^@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xf1@\x02\x05\xf5\xe1\0\x01\xfe\xf2\x90\xe02caml_gr_wait_eventAA\x05\x04s\xa0@@@\x05\x04\xb9@\xa0\xa0\xb0\x01\b\xe3,loop_at_exit@\xc0\xb0\xc1@\xb0\xb3\x04\x1a\xa0\xb0\xb3\x04\x17@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xe7@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xe8\xb0\xc1@\xb0\xc1@\xb0\xb3\x04\x1a@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xe9\xb0\xb3\x05\x04\xc4@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xea@\x02\x05\xf5\xe1\0\x01\xfe\xeb\xb0\xb3\x05\x04\xc7@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xec@\x02\x05\xf5\xe1\0\x01\xfe\xed@\x02\x05\xf5\xe1\0\x01\xfe\xee@\x05\x04\xd4@\xa0\xa0\xb0\x01\b\xe4+key_pressed@\xc0\xb0\xc1@\xb0\xb3\x05\x04\xd1@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xe4\xb0\xb3\x04r@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xe5@\x02\x05\xf5\xe1\0\x01\xfe\xe6@\x05\x04\xe1@\xa0\xa0\xb0\x01\b\xe5%sound@\xc0\xb0\xc1@\xb0\xb3\x05\x04\xc1@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xdf\xb0\xc1@\xb0\xb3\x05\x04\xc6@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xe0\xb0\xb3\x05\x04\xe6@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xe1@\x02\x05\xf5\xe1\0\x01\xfe\xe2@\x02\x05\xf5\xe1\0\x01\xfe\xe3\x90\xe0-caml_gr_soundBA\x05\x04\xb1\xa0@\xa0@@@\x05\x04\xf8@\xa0\xa0\xb0\x01\b\xe60auto_synchronize@\xc0\xb0\xc1@\xb0\xb3\x04\x93@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xdc\xb0\xb3\x05\x04\xf8@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xdd@\x02\x05\xf5\xe1\0\x01\xfe\xde@\x05\x05\x05@\xa0\xa0\xb0\x01\b\xe7+synchronize@\xc0\xb0\xc1@\xb0\xb3\x05\x05\x02@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xd9\xb0\xb3\x05\x05\x05@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xda@\x02\x05\xf5\xe1\0\x01\xfe\xdb\x90\xe03caml_gr_synchronizeAA\x05\x04\xd0\xa0@@@\x05\x05\x16@\xa0\xa0\xb0\x01\b\xe8,display_mode@\xc0\xb0\xc1@\xb0\xb3\x04\xb1@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xd6\xb0\xb3\x05\x05\x16@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xd7@\x02\x05\xf5\xe1\0\x01\xfe\xd8\x90\xe04caml_gr_display_modeAA\x05\x04\xe1\xa0@@@\x05\x05'@\xa0\xa0\xb0\x01\b\xe9-remember_mode@\xc0\xb0\xc1@\xb0\xb3\x04\xc2@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xd3\xb0\xb3\x05\x05'@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xd4@\x02\x05\xf5\xe1\0\x01\xfe\xd5\x90\xe05caml_gr_remember_modeAA\x05\x04\xf2\xa0@@@\x05\x058@\xa0\xb1\xb0\x01\b\xea'context@\b\0\0,\0@@@A@@@\x05\x05=@@\xa0@@A\xa0\xa0\xb0\x01\b\xeb*open_graph@\xc0\xb0\xc1@\xb0\xb3\x90\xb0O&string@@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xd0\xb0\xb3\x90\xb0F$unit@@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xd1@\x02\x05\xf5\xe1\0\x01\xfe\xd2@\x05\x05Q@\xa0\xa0\xb0\x01\b\xec+open_canvas@\xc0\xb0\xc1@\xb0\xb3\xb1\xb1\x90\xb0@+Js_of_ocamlA\"Js@!t\0\xff\xa0\xb0\xb3\xb1\xb1\x04\n(Dom_htmlC-canvasElement\0\xff@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xcc@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xcd\xb0\xb3\x04\x1f@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xce@\x02\x05\xf5\xe1\0\x01\xfe\xcf@\x05\x05m@\xa0\xa0\xb0\x01\b\xed+get_context@\xc0\xb0\xc1@\xb0\xb3\x04)@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xc9\xb0\xb3\x90\x04@@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xca@\x02\x05\xf5\xe1\0\x01\xfe\xcb@\x05\x05{@\xa0\xa0\xb0\x01\b\xee+set_context@\xc0\xb0\xc1@\xb0\xb3\x04\x0b@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xc6\xb0\xb3\x04:@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xc7@\x02\x05\xf5\xe1\0\x01\xfe\xc8@\x05\x05\x88@\xa0\xa0\xb0\x01\b\xef$loop@\xc0\xb0\xc1@\xb0\xb3\x90\xb0I$list@\xa0\xb0\xb3\x04\xe9@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xbe@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xbf\xb0\xc1@\xb0\xc1@\xb0\xb3\x04\xec@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xc0\xb0\xb3\x04U@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xc1@\x02\x05\xf5\xe1\0\x01\xfe\xc2\xb0\xb3\x04X@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xc3@\x02\x05\xf5\xe1\0\x01\xfe\xc4@\x02\x05\xf5\xe1\0\x01\xfe\xc5@\x05\x05\xa6@\xa0\xa0\xb0\x01\b\xf0)mouse_pos@\xc0\xb0\xc1@\xb0\xb3\x04b@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb8\xb0\xb3\xb1\x90\xb0@#LwtA!t\0\xff\xa0\xb0\x92\xa0\xb0\xb3\x90\xb0A#int@@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xba\xa0\xb0\xb3\x04\x07@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb9@\x02\x05\xf5\xe1\0\x01\xfe\xbb@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xbc@\x02\x05\xf5\xe1\0\x01\xfe\xbd@\x05\x05\xc6@\xa0\xa0\xb0\x01\b\xf1+button_down@\xc0\xb0\xc1@\xb0\xb3\x04\x82@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb4\xb0\xb3\xb1\x90\xb0@#LwtA!t\0\xff\xa0\xb0\xb3\x90\xb0E$bool@@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb5@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb6@\x02\x05\xf5\xe1\0\x01\xfe\xb7@\x05\x05\xdf@\xa0\xa0\xb0\x01\b\xf2(read_key@\xc0\xb0\xc1@\xb0\xb3\x04\x9b@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb0\xb0\xb3\xb1\x90\xb0@#LwtA!t\0\xff\xa0\xb0\xb3\x90\xb0B$char@@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb1@\x90@\x02\x05\xf5\xe1\0\x01\xfe\xb2@\x02\x05\xf5\xe1\0\x01\xfe\xb3@\x05\x05\xf8@@\x84\x95\xa6\xbe\0\0\x01\xef\0\0\0U\0\0\x01,\0\0\0\xf9\xa0\xa0+Graphics_js\x900\xa9x\x12\xa7pQ\x955\x19\xd4\x02\xd5\xd2\xeb;1\xa0\xa0$Unix\x900Z\x9b\xdf\xb6\xa1\x90zYdQ~22\xea\xcb\x14\xa0\xa0%Uchar\x900\x84\x83\x86I\xf95\x1d\xe1f\xbf\xa8\xb9\xf2\xc8M\xb4\xa0\xa0+Typed_array\x900g\xabpj\x9e\xa6r\xf5\x1d\xc1\xeb\xbc\x8bA\\V\xa0\xa0&Result\x900\xe5KJ\xcc_\xb3bJEHo)\x17\xff9\x1a\xa0\xa0*Pervasives\x900\x07\xea\x9e \xae\x94\xd6,5\xcf\xec\xbe}f\xd3\xea\xa0\xa0,Lwt_sequence\x900T63\xfevs\x81\x03W\x92\x10\xe4?\x98n\x81\xa0\xa0#Lwt\x900E\xb8\x19\xaa.\x0f\xda\x0bl0\xafRN4\x93\xd8\xa0\xa0+Js_of_ocaml\x900\x11YT\x94\xa3\x8f\x02\xbc\xf7\xfb5#+r\xd4\xfa\xa0\xa0\"Js\x900\xd5\x182\xa1\xc7\xc6\x10x\xdfu\xf8O\x87\xdd4\xe6\xa0\xa0(Graphics\x900v\xab\xd6v#\xff\xd1\xd9Td\xa5\b\xafBg\xfe\xa0\xa0$File\x900\xe8\x14LT\xea\x81\xc6\x0e_J]\xde(\xd9\x8c\xbe\xa0\xa0(Dom_html\x900\xb2\x7f@\xc1x\x1eA\xe4\x14m\x8e\x86\xa9[\xe6\x93\xa0\xa0#Dom\x900`D\xa7\xfc\x85U\x8b0\x87\x89\xa36\xbd\xd8v\xc1\xa0\xa0'Complex\x900\0\xbc\x89z=\x9c<\xeeV\x14\xe7\xf1\x91\xf8\x9a\xb7\xa0\xa08CamlinternalFormatBasics\x900\xcb\xd5\xf2\xd6\xb6I\x92R\"\xe1\xe9\xfbc\xb8\x9d\xb6\xa0\xa0(Bigarray\x900GM\xe5\n\x14h&\x8d\xbf_mdo\xe9\x0e @\x84\x95\xa6\xbe\0\0\0\x03\0\0\0\x01\0\0\0\x03\0\0\0\x03\xa0B@");
    return}
  (function(){return this}()));
