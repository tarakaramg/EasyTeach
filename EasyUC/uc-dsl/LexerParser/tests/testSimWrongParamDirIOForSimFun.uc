direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

direct d2 {
in  x@bla()
out bli()@x
}

direct D2 {D2:d2}

adversarial iio {
in  bla()
out bli()
}

functionality R(F:D) implements D {

 party P serves D {

  initial state In {
  match message with othermsg => {fail.} end
  }
 }
}

functionality I() implements D2 iio {

  initial state In {
  match message with othermsg => {fail.} end
  }
}

simulator S uses iio simulates R(I) {

  initial state In {
  match message with iio.othermsg => {fail.} end
  }

}
