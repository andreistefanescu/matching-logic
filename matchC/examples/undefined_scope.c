void main() {
  int *p;
  { int x; p = &x; }
  *p = 0;
}

