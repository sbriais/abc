(* 
#  This program is free software; you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation; either version 2 of the License, or
#  (at your option) any later version.
#
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program; if not, write to the Free Software
#  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307,
#  USA. 
*)

class virtual formatter = 
object(self)
  method virtual print_string : string -> unit
  method virtual print_newline : unit -> unit
  method virtual print_flush : unit -> unit
  method virtual open_box : int -> unit
  method virtual close_box : unit -> unit
  method virtual force_newline : unit -> unit
  method virtual print_space : unit -> unit
  method virtual print_break : int -> int -> unit
  method virtual print_if_newline : unit -> unit
end

class make_formatter = fun (p_string,p_newline,p_flush,b_open,b_close,f_newline,p_space,p_break,p_if_newline) ->
object(self)
  inherit formatter
  method print_string = p_string
  method print_newline = p_newline
  method print_flush = p_flush
  method open_box = b_open
  method close_box = b_close
  method force_newline = f_newline
  method print_space = p_space
  method print_break = p_break
  method print_if_newline = p_if_newline
end

let format = ref (new make_formatter (Format.print_string,
				      Format.print_newline,
				      Format.print_flush,
				      Format.open_box,
				      Format.close_box,
				      Format.force_newline,
				      Format.print_space,
				      Format.print_break,
				      Format.print_if_newline))
