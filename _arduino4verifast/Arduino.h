typedef unsigned char uint8_t;

#define HIGH 0x1
#define LOW  0x0

#define INPUT 0x0
#define OUTPUT 0x1
#define INPUT_PULLUP 0x2

void init(void);
  //@ requires true;
  //@ ensures true;

void pinMode(uint8_t pin, uint8_t mode);
  //@ requires (0 <= pin && pin <= 13) &*& (mode == INPUT || mode == OUTPUT || mode == INPUT_PULLUP);
  //@ ensures true;

void digitalWrite(uint8_t pin, uint8_t value);
  //@ requires (0 <= pin && pin <= 13) &*& (value == HIGH || value == LOW);
  //@ ensures true;

void delay(unsigned long ms);
  //@ requires ms > 0;
  //@ ensures true;
