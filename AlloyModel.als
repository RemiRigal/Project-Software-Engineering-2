//Class for current time and date for reservation and ride
sig string{}

sig Date{}

//Class of car Reservation
sig Reservation{
driver: one Driver,
car: one Car,
date: one Date,
}
//Class of car Research
//sig Research{
//driver: one Driver,
//locationResearch: one Position,
//maxDistance : one Int,
//}

//Class of Cancel car reservation
sig CancelReservation{
reservation: one Reservation
}

//Class of car unlocked
sig Unlock{
reservation: one Reservation
}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

sig Float{}

sig Position{
latitude: one Float,
longitude: one Float
}

one sig EnjoyCompany{
stations: set SafeArea,
cars: set Car,
}

sig Driver{
//name: one string,
//email: one string,
//drivingLicense: one Int,
//idCard : one Int,
//credential: one Int,
//password: one string,
position: one Position,
//rideInfo: lone Ride
}

sig Car{
position: one Position,
//batteryCharge: one Int,
passengersNb: one Int,
navigationScreen: one NavigationScreen,
isLocked: one Bool,
isParked: one Bool,
isPlugged: one Bool,
plug: lone Plug
}
{#passengersNb <5}

sig NavigationScreen{
savingMoneyOption: one Bool,
destination: lone Position
}

sig SafeArea{
position: one Position,
places: one Int,
}
{places >0}

sig ChargingStation extends SafeArea{
capacity: set Plug,
chargingCars: set Car
}
{#chargingCars <= #capacity}

sig Plug{}

//sig Ride{
//driver: one Driver,
//car: one Car,
//discount: one Int,
//charge: one Int,
//timeRide: one Int,
//priceRide: one Float,
//amountMoneyMin: one Float
//}


fact noChargingCarInUse{
	no s: ChargingStation, r: Reservation | r.car.isLocked = False and  r.car not in s.chargingCars
} 

fact noCarsInSamePosition{
	no disj c1, c2: Car | c1.position = c2.position
}

fact noSameReservation{
	no disj r1, r2: Reservation | (r1.date = r2.date)
}

fact noSameCancel{
	no disj c1, c2: CancelReservation | c1.reservation = c2.reservation
}

fact noSameUnlock{
	no disj u1,u2: Unlock | u1.reservation = u2.reservation
}

fact noSameScreen{
	no disj c1, c2: Car | c1.navigationScreen = c2.navigationScreen
}

fact noSceenWithoutCar{
	#NavigationScreen = #Car 
}

fact noCarWithoutCompany{
	all c: Car | c in EnjoyCompany.cars 
}


fact noSafeAreaWithoutCompany{
	all s: SafeArea| s in EnjoyCompany.stations 
}


fact CancelsReservation{
	all c: CancelReservation | c.reservation.car.isLocked = True and  c.reservation.car.isParked = True
}

fact noPlugWithoutChargeStation{
	all p: Plug | p in ChargingStation.capacity 
}

fact NoPassengerIfNoReservation{
	all c: Car | c.reservation = none implies c.passengersNb=0
}

fact LockImpliesPark{
	all c: Car | c.isLocked = True implies c.isParked = True
}

fact NoCancelReservationAndUnlock{
	no r: Reservation | r in CancelReservation.reservation and r in Unlock.reservation
}

fact NoCarPlugInIfNoPlug{
	all c: Car | c.plug = none <=> c.isPlugged = False
}

fact NoSaveOptionIfLocked{
	all c: Car | c.isLocked = True implies c.navigationScreen.savingMoneyOption = False and  c.navigationScreen.destination=none
}

fact UnlockCar{
	all u: Unlock | u.reservation.driver.position = u.reservation.car.position 
}

pred show{
#Driver = 3
#SafeArea = 1
#Reservation=2
#Car= 3
}
pred showGeneric {
#Driver = 1
#EnjoyCompany = 1
#CancelReservation=1
}
run show

