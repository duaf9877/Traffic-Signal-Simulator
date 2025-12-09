import tkinter as tk
from tkinter import ttk, messagebox
import threading
import time
import random
from enum import Enum
from collections import deque

class VehicleType(Enum):
    CAR = "Car"
    BUS = "Bus"
    MOTORCYCLE = "Motorcycle"
    AMBULANCE = "Ambulance"

class TrafficLight(Enum):
    RED = "red"
    YELLOW = "yellow"
    GREEN = "green"

class TrafficDirection(Enum):
    NORTH = "north"
    SOUTH = "south"
    EAST = "east"
    WEST = "west"

class Vehicle:
    def _init_(self, vehicle_id, vehicle_type, direction, canvas):
        self.id = vehicle_id
        self.type = vehicle_type
        self.direction = direction
        self.canvas = canvas
        self.x, self.y = self.get_start_position()
        self.width, self.height = self.get_size()
        self.color = self.get_color()
        self.speed = self.get_speed()
        self.at_intersection = False
        self.crossed = False
        self.paused = False
        self.waiting_at_intersection = False
        self.crossing_intersection = False
        self.rect = None
        self.label = None
        self.draw()
        
    def get_start_position(self):
        if self.direction == TrafficDirection.NORTH:
            return 250, 600
        elif self.direction == TrafficDirection.SOUTH:
            return 250, 0
        elif self.direction == TrafficDirection.EAST:
            return 0, 250
        elif self.direction == TrafficDirection.WEST:
            return 600, 250
    
    def get_size(self):
        if self.type == VehicleType.CAR:
            return 40, 20
        elif self.type == VehicleType.BUS:
            return 60, 25
        elif self.type == VehicleType.MOTORCYCLE:
            return 30, 15
        elif self.type == VehicleType.AMBULANCE:
            return 45, 22
    
    def get_color(self):
        colors = {
            VehicleType.CAR: "blue",
            VehicleType.BUS: "green",
            VehicleType.MOTORCYCLE: "orange",
            VehicleType.AMBULANCE: "red"
        }
        return colors[self.type]
    
    def get_speed(self):
        speeds = {
            VehicleType.CAR: 2,
            VehicleType.BUS: 1.5,
            VehicleType.MOTORCYCLE: 3,
            VehicleType.AMBULANCE: 4
        }
        return speeds[self.type]
    
    def draw(self):
        if self.rect:
            try:
                self.canvas.delete(self.rect)
                self.canvas.delete(self.label)
            except Exception:
                pass
        
        if self.direction in [TrafficDirection.NORTH, TrafficDirection.SOUTH]:
            self.rect = self.canvas.create_rectangle(
                self.x - self.width//2, self.y - self.height//2,
                self.x + self.width//2, self.y + self.height//2,
                fill=self.color, outline="black", width=2
            )
        else:
            self.rect = self.canvas.create_rectangle(
                self.x - self.height//2, self.y - self.width//2,
                self.x + self.height//2, self.y + self.width//2,
                fill=self.color, outline="black", width=2
            )
        
        self.label = self.canvas.create_text(
            self.x, self.y,
            text=self.type.value[0],
            fill="white",
            font=("Arial", 10, "bold")
        )
    
    def move(self):
        if self.paused or self.crossed:
            return
        
        if self.direction == TrafficDirection.NORTH:
            self.y -= self.speed
        elif self.direction == TrafficDirection.SOUTH:
            self.y += self.speed
        elif self.direction == TrafficDirection.EAST:
            self.x += self.speed
        elif self.direction == TrafficDirection.WEST:
            self.x -= self.speed
        
        # Check if approaching intersection
        intersection_approach = 50
        if self.direction == TrafficDirection.NORTH and 200 < self.y <= 300 + intersection_approach:
            self.at_intersection = True
        elif self.direction == TrafficDirection.SOUTH and 200 - intersection_approach <= self.y < 300:
            self.at_intersection = True
        elif self.direction == TrafficDirection.EAST and 200 - intersection_approach <= self.x < 300:
            self.at_intersection = True
        elif self.direction == TrafficDirection.WEST and 200 < self.x <= 300 + intersection_approach:
            self.at_intersection = True
        else:
            self.at_intersection = False
        
        # Check if crossed completely
        if (self.x < -50 or self.x > 550 or self.y < -50 or self.y > 550):
            self.crossed = True
            try:
                self.canvas.delete(self.rect)
                self.canvas.delete(self.label)
            except Exception:
                pass
            return
        
        self.draw()

class TrafficSignalSimulator:
    def _init_(self, root):
        self.root = root
        self.root.title("Traffic Signal Simulation OS Project")
        self.root.geometry("1200x700")
        
        # Control variables
        self.simulation_running = False
        self.deadlock_detected = False
        self.ambulance_active = False
        self.pause_all = False
        self.vehicle_counter = 0
        self.light_change_lock = threading.Lock()
        self.vehicles_crossing = 0
        self.mutex_popup_shown = False
        
        # Intersection control
        self.intersection_semaphore = threading.Semaphore(3)
        self.intersection_mutex = threading.Lock()
        self.vehicles_in_intersection = []
        
        # Waiting queues for each direction
        self.waiting_queues = {
            TrafficDirection.NORTH: [],
            TrafficDirection.SOUTH: [],
            TrafficDirection.EAST: [],
            TrafficDirection.WEST: []
        }
        self.queue_lock = threading.Lock()
        
        # Traffic lights
        self.traffic_lights = {
            TrafficDirection.NORTH: TrafficLight.RED,
            TrafficDirection.SOUTH: TrafficLight.RED,
            TrafficDirection.EAST: TrafficLight.GREEN,
            TrafficDirection.WEST: TrafficLight.GREEN
        }
        
        self.current_green_directions = [TrafficDirection.EAST, TrafficDirection.WEST]
        
        # Vehicle lists
        self.vehicles = []
        self.vehicle_threads = []
        
        # Statistics
        self.stats = {
            "cars": 0,
            "buses": 0,
            "motorcycles": 0,
            "ambulances": 0,
            "vehicles_crossed": 0,
            "deadlocks": 0,
            "mutex_acquisitions": 0
        }
        
        self.setup_gui()
        self.setup_intersection()
        self.start_traffic_light_cycle()
    
    def setup_gui(self):
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Left panel
        left_panel = ttk.LabelFrame(main_frame, text="Controls", width=300)
        left_panel.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        left_panel.pack_propagate(False)
        
        # Vehicle spawn buttons
        spawn_frame = ttk.LabelFrame(left_panel, text="Spawn Vehicles")
        spawn_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(spawn_frame, text="Spawn Car", 
                  command=lambda: self.spawn_vehicle(VehicleType.CAR)).pack(fill=tk.X, padx=5, pady=2)
        ttk.Button(spawn_frame, text="Spawn Bus", 
                  command=lambda: self.spawn_vehicle(VehicleType.BUS)).pack(fill=tk.X, padx=5, pady=2)
        ttk.Button(spawn_frame, text="Spawn Motorcycle", 
                  command=lambda: self.spawn_vehicle(VehicleType.MOTORCYCLE)).pack(fill=tk.X, padx=5, pady=2)
        ttk.Button(spawn_frame, text="Spawn Ambulance (Priority)", 
                  command=lambda: self.spawn_vehicle(VehicleType.AMBULANCE)).pack(fill=tk.X, padx=5, pady=2)
        
        # Simulation controls
        control_frame = ttk.LabelFrame(left_panel, text="Simulation Controls")
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(control_frame, text="Start Simulation", 
                  command=self.start_simulation).pack(fill=tk.X, padx=5, pady=2)
        ttk.Button(control_frame, text="Pause Simulation", 
                  command=self.pause_simulation).pack(fill=tk.X, padx=5, pady=2)
        ttk.Button(control_frame, text="Resume Simulation", 
                  command=self.resume_simulation).pack(fill=tk.X, padx=5, pady=2)
        ttk.Button(control_frame, text="Clear All Vehicles", 
                  command=self.clear_vehicles).pack(fill=tk.X, padx=5, pady=2)
        
        # Deadlock recovery
        recovery_frame = ttk.LabelFrame(left_panel, text="Deadlock Recovery")
        recovery_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(recovery_frame, text="Recover from Deadlock", 
                  command=self.recover_from_deadlock).pack(fill=tk.X, padx=5, pady=2)
        
        # Statistics display
        stats_frame = ttk.LabelFrame(left_panel, text="Statistics")
        stats_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.stats_labels = {}
        stats_texts = [
            ("Cars:", "cars"),
            ("Buses:", "buses"),
            ("Motorcycles:", "motorcycles"),
            ("Ambulances:", "ambulances"),
            ("Crossed:", "vehicles_crossed"),
            ("Deadlocks:", "deadlocks"),
            ("Mutex Acquisitions:", "mutex_acquisitions")
        ]
        
        for text, key in stats_texts:
            frame = ttk.Frame(stats_frame)
            frame.pack(fill=tk.X, padx=5, pady=2)
            ttk.Label(frame, text=text, width=20).pack(side=tk.LEFT)
            self.stats_labels[key] = ttk.Label(frame, text="0", width=10)
            self.stats_labels[key].pack(side=tk.RIGHT)
        
        # Status display
        status_frame = ttk.LabelFrame(left_panel, text="System Status")
        status_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.status_label = ttk.Label(status_frame, text="Simulation Stopped", relief=tk.SUNKEN)
        self.status_label.pack(fill=tk.X, padx=5, pady=5)
        
        self.semaphore_label = ttk.Label(status_frame, text="Semaphore: 3 available", relief=tk.SUNKEN)
        self.semaphore_label.pack(fill=tk.X, padx=5, pady=5)
        
        self.queue_label = ttk.Label(status_frame, text="Waiting: N:0 S:0 E:0 W:0", relief=tk.SUNKEN)
        self.queue_label.pack(fill=tk.X, padx=5, pady=5)
        
        # Right panel
        right_panel = ttk.Frame(main_frame)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # Canvas
        self.canvas = tk.Canvas(right_panel, width=500, height=500, bg="white", highlightthickness=1, highlightbackground="black")
        self.canvas.pack(pady=10)
        
        # Traffic lights display
        lights_frame = ttk.LabelFrame(right_panel, text="Traffic Lights Status")
        lights_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.light_labels = {}
        light_frame = ttk.Frame(lights_frame)
        light_frame.pack(fill=tk.X, padx=10, pady=5)
        
        for direction in TrafficDirection:
            frame = ttk.Frame(light_frame)
            frame.pack(side=tk.LEFT, expand=True)
            ttk.Label(frame, text=direction.value.title()).pack()
            self.light_labels[direction] = tk.Canvas(frame, width=30, height=30, highlightthickness=1)
            self.light_labels[direction].pack()
        
        self.update_traffic_lights_display()
    
    def setup_intersection(self):
        self.canvas.create_rectangle(200, 0, 300, 500, fill="gray", outline="black")
        self.canvas.create_rectangle(0, 200, 500, 300, fill="gray", outline="black")
        self.canvas.create_rectangle(200, 200, 300, 300, fill="darkgray", outline="black", width=2)
        
        for i in range(0, 500, 40):
            if 200 <= i <= 260 or 340 <= i <= 500:
                self.canvas.create_line(250, i, 250, i+20, fill="white", width=2)
                self.canvas.create_line(i, 250, i+20, 250, fill="white", width=2)
        
        self.canvas.create_text(250, 50, text="NORTH", font=("Arial", 12, "bold"))
        self.canvas.create_text(250, 450, text="SOUTH", font=("Arial", 12, "bold"))
        self.canvas.create_text(50, 250, text="WEST", font=("Arial", 12, "bold"))
        self.canvas.create_text(450, 250, text="EAST", font=("Arial", 12, "bold"))
    
    def update_traffic_lights_display(self):
        for direction, light in self.traffic_lights.items():
            canvas = self.light_labels[direction]
            canvas.delete("all")
            color = light.value
            canvas.create_oval(5, 5, 25, 25, fill=color, outline="black")
    
    def update_queue_display(self):
        with self.queue_lock:
            n = len(self.waiting_queues[TrafficDirection.NORTH])
            s = len(self.waiting_queues[TrafficDirection.SOUTH])
            e = len(self.waiting_queues[TrafficDirection.EAST])
            w = len(self.waiting_queues[TrafficDirection.WEST])
        self.queue_label.config(text=f"Waiting: N:{n} S:{s} E:{e} W:{w}")
    
    def start_traffic_light_cycle(self):
        def cycle_lights():
            while True:
                if self.simulation_running and not self.pause_all and not self.deadlock_detected:
                    # Wait for all vehicles from current green directions to clear
                    self.wait_for_crossing_vehicles()
                    
                    # East/West green
                    with self.light_change_lock:
                        self.current_green_directions = [TrafficDirection.EAST, TrafficDirection.WEST]
                        self.traffic_lights[TrafficDirection.EAST] = TrafficLight.GREEN
                        self.traffic_lights[TrafficDirection.WEST] = TrafficLight.GREEN
                        self.traffic_lights[TrafficDirection.NORTH] = TrafficLight.RED
                        self.traffic_lights[TrafficDirection.SOUTH] = TrafficLight.RED
                        self.update_traffic_lights_display()
                    
                    # Let all waiting vehicles from this direction pass
                    self.allow_direction_batch(TrafficDirection.EAST)
                    self.allow_direction_batch(TrafficDirection.WEST)
                    
                    # Wait a bit before changing
                    time.sleep(5)
                    
                    # Yellow warning
                    if self.simulation_running and not self.pause_all:
                        self.traffic_lights[TrafficDirection.EAST] = TrafficLight.YELLOW
                        self.traffic_lights[TrafficDirection.WEST] = TrafficLight.YELLOW
                        self.update_traffic_lights_display()
                        time.sleep(2)
                    
                    # Wait for crossing vehicles to finish
                    self.wait_for_crossing_vehicles()
                    
                    # North/South green
                    if self.simulation_running and not self.pause_all:
                        with self.light_change_lock:
                            self.current_green_directions = [TrafficDirection.NORTH, TrafficDirection.SOUTH]
                            self.traffic_lights[TrafficDirection.NORTH] = TrafficLight.GREEN
                            self.traffic_lights[TrafficDirection.SOUTH] = TrafficLight.GREEN
                            self.traffic_lights[TrafficDirection.EAST] = TrafficLight.RED
                            self.traffic_lights[TrafficDirection.WEST] = TrafficLight.RED
                            self.update_traffic_lights_display()
                        
                        # Let all waiting vehicles from this direction pass
                        self.allow_direction_batch(TrafficDirection.NORTH)
                        self.allow_direction_batch(TrafficDirection.SOUTH)
                        
                        time.sleep(5)
                        
                        # Yellow warning
                        if self.simulation_running and not self.pause_all:
                            self.traffic_lights[TrafficDirection.NORTH] = TrafficLight.YELLOW
                            self.traffic_lights[TrafficDirection.SOUTH] = TrafficLight.YELLOW
                            self.update_traffic_lights_display()
                            time.sleep(2)
                else:
                    time.sleep(0.1)
        
        light_thread = threading.Thread(target=cycle_lights, daemon=True)
        light_thread.start()
    
    def wait_for_crossing_vehicles(self):
        # Wait until all vehicles currently crossing are done
        while self.vehicles_crossing > 0:
            time.sleep(0.1)
    
    def allow_direction_batch(self, direction):
        # Signal all waiting vehicles from this direction to go
        with self.queue_lock:
            vehicles_to_release = list(self.waiting_queues[direction])
            self.waiting_queues[direction].clear()
        
        # Release vehicles one by one with small delay
        for vehicle in vehicles_to_release:
            if not vehicle.crossed:
                vehicle.waiting_at_intersection = False
            time.sleep(0.3)
        
        self.update_queue_display()
    
    def spawn_vehicle(self, vehicle_type):
        if not self.simulation_running:
            messagebox.showwarning("Warning", "Please start the simulation first!")
            return
        
        directions = list(TrafficDirection)
        direction = random.choice(directions)
        
        self.vehicle_counter += 1
        vehicle_id = f"{vehicle_type.value}_{self.vehicle_counter}"
        
        vehicle = Vehicle(vehicle_id, vehicle_type, direction, self.canvas)
        self.vehicles.append(vehicle)
        
        self.stats[vehicle_type.value.lower() + "s"] += 1
        self.update_stats_display()
        
        thread = threading.Thread(target=self.vehicle_behavior, args=(vehicle,), daemon=True)
        self.vehicle_threads.append(thread)
        thread.start()
    
    def vehicle_behavior(self, vehicle):
        while not vehicle.crossed:
            if self.pause_all and vehicle.type != VehicleType.AMBULANCE:
                time.sleep(0.1)
                continue
            
            if self.ambulance_active and vehicle.type != VehicleType.AMBULANCE:
                vehicle.paused = True
                time.sleep(0.1)
                continue
            else:
                vehicle.paused = False
            
            vehicle.move()
            
            if vehicle.at_intersection and not vehicle.crossed and not vehicle.waiting_at_intersection:
                if vehicle.type == VehicleType.AMBULANCE:
                    self.handle_ambulance(vehicle)
                else:
                    self.handle_regular_vehicle(vehicle)
            
            time.sleep(0.05)
        
        # Clean up when crossed
        with self.queue_lock:
            for direction in self.waiting_queues:
                if vehicle in self.waiting_queues[direction]:
                    self.waiting_queues[direction].remove(vehicle)
        self.update_queue_display()
    
    def handle_regular_vehicle(self, vehicle):
        # Check traffic light
        light = self.traffic_lights[vehicle.direction]
        
        if light == TrafficLight.RED or light == TrafficLight.YELLOW:
            # Add to waiting queue
            with self.queue_lock:
                if vehicle not in self.waiting_queues[vehicle.direction]:
                    self.waiting_queues[vehicle.direction].append(vehicle)
                    vehicle.waiting_at_intersection = True
            self.update_queue_display()
            self.check_deadlock()
            
            # Wait for green light and release from queue
            while vehicle.waiting_at_intersection and not vehicle.crossed:
                if self.pause_all or self.deadlock_detected:
                    time.sleep(0.1)
                    continue
                time.sleep(0.1)
        
        # Green light - proceed through intersection
        if not vehicle.crossed:
            self.cross_intersection(vehicle)
    
    def handle_ambulance(self, vehicle):
        self.ambulance_active = True
        
        # Show ambulance priority message
        self.root.after(0, lambda: messagebox.showinfo("Ambulance Priority", 
            f"Ambulance detected! All vehicles paused.\nAmbulance from {vehicle.direction.value.upper()} has priority."))
        
        # Clear intersection
        with self.intersection_mutex:
            self.vehicles_in_intersection.clear()
        
        # Cross immediately
        self.cross_intersection(vehicle)
        
        time.sleep(1)
        self.ambulance_active = False
    
    def cross_intersection(self, vehicle):
        # Acquire semaphore
        self.intersection_semaphore.acquire()
        self.vehicles_crossing += 1
        
        with self.intersection_mutex:
            self.vehicles_in_intersection.append(vehicle.id)
            self.stats["mutex_acquisitions"] += 1
            self.update_stats_display()
            
            if not self.mutex_popup_shown and vehicle.type != VehicleType.AMBULANCE:
                self.root.after(0, self.show_mutex_popup, vehicle.id)
                self.mutex_popup_shown = True
        
        vehicle.crossing_intersection = True
        
        # Move through intersection
        steps = 60
        for _ in range(steps):
            if self.pause_all and vehicle.type != VehicleType.AMBULANCE:
                time.sleep(0.1)
                continue
            if not vehicle.crossed:
                vehicle.move()
            time.sleep(0.03)
        
        vehicle.crossing_intersection = False
        
        # Release semaphore
        with self.intersection_mutex:
            if vehicle.id in self.vehicles_in_intersection:
                self.vehicles_in_intersection.remove(vehicle.id)
        
        self.vehicles_crossing -= 1
        self.intersection_semaphore.release()
        
        self.stats["vehicles_crossed"] += 1
        self.update_stats_display()
    
    def check_deadlock(self):
        if self.deadlock_detected:
            return
        
        # Count total waiting vehicles
        total_waiting = 0
        waiting_by_direction = {}
        
        with self.queue_lock:
            for direction in self.waiting_queues:
                count = len(self.waiting_queues[direction])
                waiting_by_direction[direction] = count
                total_waiting += count
        
        # Deadlock if 6+ vehicles waiting (at least 2 in multiple directions)
        if total_waiting >= 6:
            directions_with_vehicles = sum(1 for count in waiting_by_direction.values() if count >= 2)
            
            if directions_with_vehicles >= 2:
                self.deadlock_detected = True
                self.stats["deadlocks"] += 1
                self.update_stats_display()
                self.root.after(0, self.show_deadlock_popup, waiting_by_direction)
    
    def show_mutex_popup(self, vehicle_id):
        messagebox.showinfo("Mutex Acquired", 
                           f"Vehicle {vehicle_id} acquired mutex for intersection access.")
    
    def show_deadlock_popup(self, waiting_by_direction):
        self.pause_all = True
        self.gray_out_vehicles()
        
        msg = "DEADLOCK DETECTED!\n\n"
        msg += "Vehicles waiting at intersection:\n"
        for direction, count in waiting_by_direction.items():
            if count > 0:
                msg += f"  {direction.value.upper()}: {count} vehicles\n"
        msg += "\nClick 'Recover from Deadlock' to resolve."
        
        messagebox.showwarning("DEADLOCK!", msg)
    
    def gray_out_vehicles(self):
        for vehicle in self.vehicles:
            if not vehicle.crossed and vehicle.rect:
                try:
                    self.canvas.itemconfig(vehicle.rect, fill="gray")
                except Exception:
                    pass
    
    def recover_from_deadlock(self):
        if not self.deadlock_detected:
            messagebox.showinfo("No Deadlock", "No deadlock detected!")
            return
        
        # Find direction with most waiting vehicles
        max_waiting = 0
        priority_direction = None
        
        with self.queue_lock:
            for direction, queue in self.waiting_queues.items():
                if len(queue) > max_waiting:
                    max_waiting = len(queue)
                    priority_direction = direction
        
        if priority_direction:
            # Show recovery message
            msg = f"Deadlock Recovery Initiated!\n\n"
            msg += f"Giving priority to: {priority_direction.value.upper()}\n"
            msg += f"Releasing {max_waiting} vehicles from this direction first."
            
            messagebox.showinfo("Recovery in Progress", msg)
            
            # Force light change to priority direction
            with self.light_change_lock:
                # Determine opposite direction
                if priority_direction in [TrafficDirection.NORTH, TrafficDirection.SOUTH]:
                    opposite = TrafficDirection.SOUTH if priority_direction == TrafficDirection.NORTH else TrafficDirection.NORTH
                    self.current_green_directions = [TrafficDirection.NORTH, TrafficDirection.SOUTH]
                    self.traffic_lights[TrafficDirection.NORTH] = TrafficLight.GREEN
                    self.traffic_lights[TrafficDirection.SOUTH] = TrafficLight.GREEN
                    self.traffic_lights[TrafficDirection.EAST] = TrafficLight.RED
                    self.traffic_lights[TrafficDirection.WEST] = TrafficLight.RED
                else:
                    opposite = TrafficDirection.WEST if priority_direction == TrafficDirection.EAST else TrafficDirection.EAST
                    self.current_green_directions = [TrafficDirection.EAST, TrafficDirection.WEST]
                    self.traffic_lights[TrafficDirection.EAST] = TrafficLight.GREEN
                    self.traffic_lights[TrafficDirection.WEST] = TrafficLight.GREEN
                    self.traffic_lights[TrafficDirection.NORTH] = TrafficLight.RED
                    self.traffic_lights[TrafficDirection.SOUTH] = TrafficLight.RED
                
                self.update_traffic_lights_display()
        
        # Restore vehicle colors
        for vehicle in self.vehicles:
            if not vehicle.crossed and vehicle.rect:
                try:
                    self.canvas.itemconfig(vehicle.rect, fill=vehicle.color)
                except Exception:
                    pass
        
        # Clear deadlock state
        self.deadlock_detected = False
        self.pause_all = False
        
        # Release all waiting vehicles from priority direction
        if priority_direction:
            self.allow_direction_batch(priority_direction)
        
        messagebox.showinfo("Recovery Complete", 
            f"Deadlock resolved!\nVehicles from {priority_direction.value.upper()} are now passing.")
    
    def update_stats_display(self):
        for key, label in self.stats_labels.items():
            label.config(text=str(self.stats[key]))
        
        available = getattr(self.intersection_semaphore, "_value", "?")
        try:
            used = 3 - int(available)
            self.semaphore_label.config(text=f"Semaphore: {available} available, {used} in use")
        except Exception:
            self.semaphore_label.config(text=f"Semaphore status: {available}")
    
    def start_simulation(self):
        self.simulation_running = True
        self.status_label.config(text="Simulation Running")
        messagebox.showinfo("Simulation Started", "Traffic simulation is now running!")
    
    def pause_simulation(self):
        self.pause_all = True
        self.status_label.config(text="Simulation Paused")
    
    def resume_simulation(self):
        self.pause_all = False
        self.deadlock_detected = False
        self.status_label.config(text="Simulation Running")
    
    def clear_vehicles(self):
        for vehicle in self.vehicles:
            if not vehicle.crossed:
                try:
                    self.canvas.delete(vehicle.rect)
                    self.canvas.delete(vehicle.label)
                except Exception:
                    pass
        
        self.vehicles = [v for v in self.vehicles if v.crossed]
        
        with self.queue_lock:
            for direction in self.waiting_queues:
                self.waiting_queues[direction].clear()
        
        self.update_queue_display()
        self.update_stats_display()

def main():
    root = tk.Tk()
    app = TrafficSignalSimulator(root)
    root.mainloop()

if __name__ == "_main_":
    main()