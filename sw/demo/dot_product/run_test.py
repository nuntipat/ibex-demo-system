import sys
import serial
import numpy as np
import time

NUM_ELEMENT = 10
NUM_ITERATION = 5000
secret = np.array([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])

with serial.Serial('/dev/ttyUSB1', 115200, timeout=0.1) as ser:
    for iteration in range(1, NUM_ITERATION+1):
        if iteration % 100 == 0:
            print (f'Iteration : {iteration}/{NUM_ITERATION}')

        rand = np.random.randint(0, 256, size=NUM_ELEMENT, dtype=np.uint8)
        ser.write(rand.tobytes())
        # for i in range(NUM_ELEMENT):
        #     ser.write(rand[i].tobytes())
        #     time.sleep(0.001)

        tmp = np.zeros(NUM_ELEMENT)
        for i in range(NUM_ELEMENT):
            tmp[i] = int.from_bytes(ser.read(), byteorder='big')

        # print (rand, tmp)
        if not np.array_equal(rand, tmp):
            print ('Error: input received mismatch!!!')
            sys.exit(1)
        
        board_result = int(ser.readline().decode().strip(), base=16)
        expected_result = np.dot(secret, rand)

        # print (board_result, expected_result)
        if board_result != expected_result:
            print ('Error: incorrect result!!!')
            sys.exit(1)