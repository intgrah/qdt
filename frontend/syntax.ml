type position = {
  offset : int;
  line : int;
  column : int;
}

type span = {
  start_pos : position;
  end_pos : position;
}

type src = span option
