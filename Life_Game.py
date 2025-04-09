import pygame
import sys
import random
import time
import math
import numpy as np
import RPi.GPIO as GPIO
import asyncio
import subprocess
from bleak import BleakScanner, BleakClient
from bleak.backends.characteristic import BleakGATTCharacteristic

# 初始化 GPIO
GPIO.setmode(GPIO.BCM)

# 定義按鈕 GPIO 腳位
SWITCH_PINS = {
    "up": 26,
    "down": 6,
    "left": 19,
    "right": 13
}

# 設定 GPIO 為輸入模式
for pin in SWITCH_PINS.values():
    GPIO.setup(pin, GPIO.IN, pull_up_down=GPIO.PUD_UP)

# 設定畫面大小與細胞格子大小
WIDTH, HEIGHT = 280, 240
CELL_SIZE = 15
ROWS, COLS = HEIGHT // CELL_SIZE, WIDTH // CELL_SIZE


# 顏色設定
BLACK = (0, 0, 0)
WHITE = (255, 255, 255)
RED = (255, 0, 0)
GREEN = (0, 255, 0)
BLUE = (0, 0, 255)
PINK = (255, 0, 255)
GRID_COLOR = (50, 50, 50)

# 顏色映射
COLOR_MAP = {
    0: BLACK,   # 無細胞
    1: RED,     # 向上 (Red)
    2: PINK,    # 向左 (Pink)
    3: BLUE,    # 向右 (Blue)
    4: GREEN    # 向下 (Green)
}

## 藍芽設定------------------------------------------------------------------

# 記錄按鈕放開的時間戳
release_timestamps = {}

# 全域鎖
bluetooth_scan_lock = asyncio.Lock()

# 管理連接任務
connection_tasks = {}

# ESP32 相關設定
ESP32_CHARACTERISTIC_UUID = "6eaaf297-0cc4-417a-8165-415b75e8e702"
ESP32_MAC_ADDRESSES = ["F0:9E:9E:B3:F8:A6", "F0:9E:9E:B5:39:46",
"F0:9E:9E:B3:F1:A2", "F0:9E:9E:B4:04:AE", "F0:9E:9E:B3:F1:C2", "F0:9E:9E:B4:00:DE"]

# 紀錄 MAC address 與裝置類型的對應
A_DEVICES = ["F0:9E:9E:B3:F8:A6", "F0:9E:9E:B5:39:46"]
B_DEVICES = ["F0:9E:9E:B3:F1:A2", "F0:9E:9E:B4:04:AE"]
C_DEVICES = ["F0:9E:9E:B3:F1:C2", "F0:9E:9E:B4:00:DE"]

# 角色與按鈕對應
controller_sprites = {}
player_sprites = {}
bluetooth_assignments = {}  # 記錄按鈕與藍牙裝置的對應
connected_clients = {}

# 位置對應
POSITIONS = {
    "up": (WIDTH // 2 - 5, HEIGHT // 4 - 5),
    "down": (WIDTH // 2 - 5, HEIGHT * 3 // 4 - 5),
    "left": (WIDTH // 4 - 5, HEIGHT // 2 - 5),
    "right": (WIDTH * 3 // 4 - 5, HEIGHT // 2 - 5)
}

## 藍芽設定------------------------------------------------------------------

# 初始化 Pygame
pygame.init()
#screen = pygame.display.set_mode((WIDTH, HEIGHT))

# 視窗設定
surface_size = (320, 240)
lcd = pygame.Surface(surface_size)
SCREEN_WIDTH, SCREEN_HEIGHT = 320, 240

pygame.display.set_caption("Conway's Game of Life")
clock = pygame.time.Clock()

# 用來控制生命遊戲更新的間隔
game_update_interval = 10  # 每隔 XX 毫秒更新一次
last_game_update_time = pygame.time.get_ticks()

# Conway's Game of Life 初始狀態
cells = np.zeros((ROWS, COLS), dtype=int)
cell_types = np.full((ROWS, COLS), None)

# 畫面更新
def refresh():
    """Write the Pygame screen buffer to the framebuffer"""
    try:
        with open("/dev/fb1", "wb") as f:
            # Convert screen to 32-bit format and get buffer
            buffer = lcd.convert(32, 0).get_buffer()
            f.write(buffer)
        time.sleep(0.01)
    except Exception as e:
        print(f"Refresh error: {e}")

class Cell:
    def __init__(self,initial_cell):
        self.cells = initial_cell
        self.running = True

    def update(self):
        """更新 Conway's Game of Life 狀態"""
        new_cells = np.copy(self.cells)
        for i in range(ROWS):
            for j in range(COLS):
                neighbors = np.sum(cells[max(i-1, 0):min(i+2, ROWS), max(j-1, 0):min(j+2, COLS)]) - cells[i, j]
                if cells[i, j] == 1 and (neighbors < 2 or neighbors > 3):
                    new_cells[i, j] = 0
                elif cells[i, j] == 0 and neighbors == 3:
                    new_cells[i, j] = 1
        self.cells = new_cells # 更新狀態
        return new_cells

class Controller(pygame.sprite.Sprite):
    def __init__(self, color, x, y):
        super().__init__()
        self.image = pygame.Surface((10, 10))
        self.image.fill(color)
        self.rect = self.image.get_rect()
        self.rect.centerx = x
        self.rect.centery = y
        self.address = ""
        self.dir = ""
        self.color = WHITE

        # A 裝置的 Value
        self.counter = 0
        self.ori_counter = 0
        self.angle = 0  # 旋轉角度

        # B 裝置的 Value
        self.slide = x

        # C 裝置的 Value
        self.button = ''

    def bresenham_line(x0, y0, x1, y1):
        """Bresenham 直線演算法，返回線段經過的格子"""
        points = []
        dx, dy = abs(x1 - x0), abs(y1 - y0)
        sx, sy = (1 if x0 < x1 else -1), (1 if y0 < y1 else -1)
        err = dx - dy

        while True:
            points.append((x0, y0))
            if x0 == x1 and y0 == y1:
                break
            e2 = 2 * err
            if e2 > -dy:
                err -= dy
                x0 += sx
            if e2 < dx:
                err += dx
                y0 += sy

        return points

    def apply_rotating_line(self):
        """根據 counter 旋轉的角度繪製線，並殺死經過的細胞"""
        global cells
        self.angle = (self.counter * 10) % 360  # 旋轉角度受 counter 影響，每次增加 5 度
        cx, cy = COLS // 2, ROWS // 2
        radius = min(COLS, ROWS) // 2

        end_x = cx + int(radius * math.cos(math.radians(self.angle)))
        end_y = cy + int(radius * math.sin(math.radians(self.angle)))

        # 繪製旋轉線的過程
        for x, y in Controller.bresenham_line(cx, cy, end_x, end_y):
            if 0 <= x < COLS and 0 <= y < ROWS:
                cells[y, x] = 0  # 設為死亡狀態
                cell_types[y, x] = None
                # 繪製旋轉線
                pygame.draw.rect(lcd, WHITE, (x * CELL_SIZE, y * CELL_SIZE, CELL_SIZE, CELL_SIZE))


    def spawn_random_cluster(self,size=5):
        """在隨機位置產生 size x size 的細胞群"""
        global cells, cell_types
        x, y = random.randint(0, COLS - size), random.randint(0, ROWS - size)

        for i in range(size):
            for j in range(size):
                if random.random() > 0.3:
                    cells[y + i, x + j] = 1  # 先確認該細胞是活的
                    cell_types[y + i, x + j] = {"up": 1, "down": 2, "left": 3, "right": 4}.get(self.dir, 1)


    def update_slide_cells(self):
    #根據 slide 值增加或減少對應行的細胞，允許不同類型細胞共存
        row = int((self.slide / 255) * (ROWS - 1))

        if self.dir == "left" or self.dir == "right":
            for col in range(COLS):  # 影響整列
                cells[row, col] = 1
                cell_types[row, col] = 3 if self.dir == "left" else 4
        elif self.dir == "up" or self.dir == "down":
            col = int((self.slide / 255) * (COLS - 1))  # 計算對應的 column (橫向移動)
            for row in range(ROWS):  # 影響整行
                cells[row, col] = 1
                cell_types[row, col] = 1 if self.dir == "up" else 2


    def update(self):

        if self.address in A_DEVICES: #如果是 A 裝置的話...
            self.apply_rotating_line()


        elif self.address in B_DEVICES:
            #print("B")
            self.update_slide_cells()


        elif self.address in C_DEVICES:
            #print("C")
            if self.button == 1 or self.button == 255:
                self.button = 0
                self.spawn_random_cluster(size=10)

# 中斷連接的安全方法
async def disconnect_client(client, mac_address):
    try:
        if client.is_connected:
            await client.disconnect()
            print(f"成功中斷連接：{mac_address}")
    except Exception as e:
        print(f"中斷連接失敗 ({mac_address}): {e}")

# 正確取消任務的函式
def cancel_connection_task(mac_address):
    task = connection_tasks.get(mac_address)
    if task and not task.done():
        task.cancel()
        print(f"已取消先前的連接任務: {mac_address}")

# 全局記錄正在嘗試連線的方向，避免重複掃描
connecting_directions = set()

# 指定藍牙裝置到方向
async def assign_bluetooth_to_direction(direction, retry_count = 0):
    MAX_RETRIES = 3

    if direction in connecting_directions:
        return # 已經在連線中，不重複

    connecting_directions.add(direction)

    #async with bluetooth_scan_lock:
    try:
        async with bluetooth_scan_lock:
            print("開始掃描藍牙裝置...")
            devices = await BleakScanner.discover()
            #print("掃描結果:", [device.address for device in devices])  # 印出所有掃描到的裝置

            for device in devices:
                if device.address in ESP32_MAC_ADDRESSES and device.address not in bluetooth_assignments.values():
                    bluetooth_assignments[direction] = device.address
                    asyncio.create_task(connect_and_listen(device.address, direction))
                    print(f"成功分配 {device.address} 給 {direction}")
                    break
                else:
                    print(f"沒有找到未分配的 ESP32 裝置給 {direction}")

    except Exception as e:
        print(f"藍牙掃描錯誤: {e}")
        if "InProgress" in str(e) and retry_count < MAX_RETRIES:
            print(f"[{direction}]掃描正在進行中，{retry_count + 1}秒後重試...")
            await asyncio.sleep(1)
            await assign_bluetooth_to_direction(direction,retry_count + 1)
        else:
            print(f"[{direction}]掃描錯誤以達到最大次數或非掃描衝突錯誤")

    finally:
        connecting_directions.discard(direction)


# 處理藍牙通知
def notification_handler(direction, data: bytearray, mac_address):
    try:

        if len(data) == 1:  # 如果數據長度為 1，則直接轉換
            value = int(data[0])  # 直接取第一個 byte
        else:
            value = int(data.decode("utf-8").strip())  # 嘗試用 UTF-8 解碼
        #value = int(data.decode("utf-8").strip())
        if direction in controller_sprites:
        # 根據 MAC 地址來決定屬性
            if mac_address in A_DEVICES:
                controller_sprites[direction].dir = direction
                #print("給予 A Value")
                controller_sprites[direction].counter = value


            elif mac_address in B_DEVICES:
                controller_sprites[direction].dir = direction
                #print("給予 B Value")
                controller_sprites[direction].slide = value


            elif mac_address in C_DEVICES:
                controller_sprites[direction].dir = direction
                print("給予 C Value")
                controller_sprites[direction].button = value
                #print(direction)
            else:
                print(f"未知裝置的數據：{mac_address} - {value}")

    except ValueError:
        print(f"無效數據來自 {mac_address}：{data}")

# 連接並監聽藍牙設備
async def connect_and_listen(mac_address, direction):
    # 確保沒有重複連線任務
    cancel_connection_task(mac_address)

    MAX_CONNECT_RETRIES = 5
    retries = 0

    async def connection_task():
        nonlocal retries

        while retries < MAX_CONNECT_RETRIES:
            try:
                # 超過 5 秒未按下按鈕則停止連接嘗試
                if direction in release_timestamps and time.time() - release_timestamps[direction] > 1:
                    print(f"放開按鈕超過 1 秒，不再嘗試連接: {mac_address}")
                    break

                print(f"嘗試連接到裝置: {mac_address}")
                async with BleakClient(mac_address) as client:
                    connected_clients[mac_address] = client

                    await client.start_notify(
                        ESP32_CHARACTERISTIC_UUID,
                        lambda c, d: notification_handler(direction, d, mac_address)
                    )
                    print(f"已成功連接到裝置: {mac_address}")
                    controller_sprites[direction].address = mac_address
                    #await asyncio.sleep(0.5)
                     # 持續保持連接
                    while client.is_connected:
                        await asyncio.sleep(1)

                    print(f"連接中斷: {mac_address}")
                    break # 成功後不再重試

            except Exception as e:
                print(f"Bluetooth error ({mac_address}): {e}")
                retries += 1
                if retries >= MAX_CONNECT_RETRIES:
                    print(f"裝置 {mac_address} 連接重試次數過多，中止嘗試")
                    break
                await asyncio.sleep(1)

        if mac_address in connected_clients:
            del connected_clients[mac_address]
        #await asyncio.sleep(1)

    # 記錄新任務
    connection_tasks[mac_address] = asyncio.create_task(connection_task())



async def handle_pygame_events():
    global last_game_update_time, game_update_interval, cells

    running = True

    while running:

        lcd.fill(BLACK) # 清空畫面

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False

        for direction, pin in SWITCH_PINS.items():
            if GPIO.input(pin) == GPIO.LOW:  # 按下按鈕
                # 重設放開時間戳
                release_timestamps.pop(direction, None)

                if direction not in controller_sprites:
                    controller = Controller(WHITE, *POSITIONS[direction])
                    controller_sprites[direction] = controller

                if direction not in bluetooth_assignments and direction not in connecting_directions:
                    asyncio.create_task(assign_bluetooth_to_direction(direction))
                    print("按鈕已被按下")
            else:
                if direction in controller_sprites:
                    del controller_sprites[direction]

                if direction in bluetooth_assignments:
                    mac_address = bluetooth_assignments.pop(direction)
                    if mac_address in connected_clients:
                        del connected_clients[mac_address]
                        print("按鈕已被放開")
                        # 紀錄放開按鈕的時間戳
                        release_timestamps[direction] = time.time()




        # 檢查是否該更新生命遊戲
        current_time = pygame.time.get_ticks()
        if current_time - last_game_update_time >= game_update_interval:
            last_game_update_time = current_time
            cell = Cell(cells)  # 更新生命遊戲
            cells = cell.update()

        for controller in controller_sprites.values():
            controller.update()
            #lcd.blit(controller.image, controller.rect)

        # 繪製細胞
        for i in range(ROWS):
            for j in range(COLS):
                if cells[i, j] > 0: # 只有活細胞才繪製
                    if cell_types[i,j] is not None:
                        #cell_types[i,j] = 1
                        color = COLOR_MAP.get(cell_types[i, j], WHITE)  # 取得對應顏色，若無則預設白色
                        pygame.draw.rect(lcd, color, (j * CELL_SIZE, i * CELL_SIZE, CELL_SIZE, CELL_SIZE))

        # 畫面顯示
        refresh()
        clock.tick(60)  # 控制更新速度 ( XX FPS)
        await asyncio.sleep(0.01)

    GPIO.cleanup()
    pygame.quit()

# 主程式
async def main():
    tasks = [ handle_pygame_events()]
    await asyncio.gather(*tasks)

asyncio.run(main())
