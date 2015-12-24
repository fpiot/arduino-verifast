#include <Arduino.h>

#define LED 13
#define BLINK_DELAY_MS 500

int main() //@ : main
  //@ requires true;
  //@ ensures false;
{
	init();

	pinMode(LED, OUTPUT);

	while(1)
	  //@ invariant true;
	{
		digitalWrite(LED, HIGH);
		delay(BLINK_DELAY_MS);
		digitalWrite(LED, LOW);
		delay(BLINK_DELAY_MS);
	}

	return 0;
}
